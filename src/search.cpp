/*
 * Copyright (C) 2017-2021 Matthieu Gautier <mgautier@kymeria.fr>
 * Copyright (C) 2021 Maneesh P M <manu.pm55@gmail.com>
 * Copyright (C) 2021 Veloman Yunkan
 * Copyright (C) 2020 Emmanuel Engelhart <kelson@kiwix.org>
 * Copyright (C) 2018 Kunal Mehta <legoktm@member.fsf.org>
 * Copyright (C) 2007 Tommi Maekitalo
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * is provided AS IS, WITHOUT ANY WARRANTY; without even the implied
 * warranty of MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, and
 * NON-INFRINGEMENT.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA
 *
 */

#include <mutex>
#include <atomic>
#include <memory>
#include <zim/error.h>
#include <zim/search.h>
#include <zim/archive.h>
#include <zim/item.h>
#include "fileimpl.h"
#include "lock.h"
#include "search_internal.h"
#include "tools.h"
#include "zim/zim.h"

#include <sstream>

#include <sys/types.h>
#include <sys/stat.h>
#if !defined(_WIN32)
# include <unistd.h>
#else
# include <io.h>
#endif

#include "xapian.h"

#include "constants.h"

#define MAX_MATCHES_TO_SORT 10000

namespace zim
{
XapianDbMetadata::XapianDbMetadata(const Xapian::Database& db, std::string defaultLanguage)
    : m_language(defaultLanguage)
{
    m_valuesmap = read_valuesmap(db.get_metadata("valuesmap"));
    auto language = db.get_metadata("language");
    if (! language.empty()) {
        m_language = language;
    }
    m_stemmer = getXapianStemmer(m_language);
    m_stopwords = db.get_metadata("stopwords");
}


Xapian::Stopper* XapianDbMetadata::new_stopper() {
    // Xapian (for stopper) use a internal intrusive smart pointer with a optional ref count.
    // By default (it is not ref counted) so it is to us to delete it.
    // But if we call `release` on it, it is then ref counted and pass it to Xapian to
    // let it handle the deletion. We may delete it ourselves
    // (but as any other deleted value, we must ensure no use after delete)
    if ( !m_stopwords.empty() ){
        std::string stopWord;
        std::istringstream file(m_stopwords);
        Xapian::SimpleStopper*  stopper = new Xapian::SimpleStopper();
        while (std::getline(file, stopWord, '\n')) {
            stopper->add(stopWord);
        }
        return stopper->release();
    }
    return nullptr;
}

XapianDb::XapianDb(const Xapian::Database& db, std::string defaultLanguage)
  : m_metadata(db, defaultLanguage),
    m_db(db)
{}

InternalDataBase::InternalDataBase(const std::vector<Archive>& archives, bool verbose)
  : m_verbose(verbose)
{
    bool first = true;
    m_queryParser.set_database(m_database);
    m_queryParser.set_default_op(Xapian::Query::op::OP_AND);
    std::vector<std::recursive_mutex*> mutexes;

    for(auto& archive: archives) {
        auto database = archive.getImpl()->getXapianDb();

        if (!database) {
            continue;
        }

        if ( first ) {
            m_metadata = database->m_metadata;
            m_queryParser.set_stemmer(m_metadata.m_stemmer);
            m_queryParser.set_stemming_strategy(Xapian::QueryParser::STEM_ALL);
            m_queryParser.set_stopper(m_metadata.new_stopper());
            first = false;
        }
        m_database.add_database(database->m_db);
        mutexes.push_back(&database->m_mutex);
        m_archives.push_back(archive);
    }

    m_mutexes = MultiMutex(mutexes);
}

bool InternalDataBase::hasDatabase() const
{
  return !m_archives.empty();
}

bool InternalDataBase::hasValuesmap() const
{
  return m_metadata.hasValuesmap();
}

bool InternalDataBase::hasValue(const std::string& valueName) const
{
  return m_metadata.hasValue(valueName);
}

int InternalDataBase::valueSlot(const std::string& valueName) const
{
  return m_metadata.valueSlot(valueName);
}

std::lock_guard<MultiMutex> InternalDataBase::lock() {
  // Construct the guard with a list-initialization, so we don't have to move it
  // (which we can't do as lock_guard is not movable).
  // See https://stackoverflow.com/questions/22502606/why-is-stdlock-guard-not-movable
  return { m_mutexes, std::adopt_lock };
}

Xapian::Query InternalDataBase::parseQuery(const Query& query)
{
  Xapian::Query xquery;

  const auto unaccentedQuery = removeAccents(query.m_query);
  xquery = m_queryParser.parse_query(unaccentedQuery, Xapian::QueryParser::FLAG_CJK_NGRAM);

  if (query.m_geoquery && hasValue("geo.position")) {
    Xapian::GreatCircleMetric metric;
    Xapian::LatLongCoord centre(query.m_latitude, query.m_longitude);
    Xapian::LatLongDistancePostingSource ps(valueSlot("geo.position"), centre, metric, query.m_distance);
    Xapian::Query geoQuery(&ps);
    if (unaccentedQuery.empty()) {
      xquery = geoQuery;
    } else {
      xquery = Xapian::Query(Xapian::Query::OP_FILTER, xquery, geoQuery);
    }
  }

  return xquery;
}

Searcher::Searcher(const std::vector<Archive>& archives) :
    mp_internalDb(nullptr),
    m_verbose(false)
{
    for ( const auto& a : archives ) {
        addArchive(a);
    }
}

Searcher::Searcher(const Archive& archive) :
    mp_internalDb(nullptr),
    m_verbose(false)
{
    addArchive(archive);
}

Searcher::Searcher(const Searcher& other) = default;
Searcher& Searcher::operator=(const Searcher& other) = default;
Searcher::Searcher(Searcher&& other) = default;
Searcher& Searcher::operator=(Searcher&& other) = default;
Searcher::~Searcher() = default;

namespace
{

bool archivesAreEquivalent(const Archive& a1, const Archive& a2)
{
  return a1.getUuid() == a2.getUuid();
}

bool contains(const std::vector<Archive>& archives, const Archive& newArchive)
{
    for ( const auto& a : archives ) {
        if ( archivesAreEquivalent(a, newArchive) ) {
            return true;
        }
    }
    return false;
}

} // unnamed namespace

Searcher& Searcher::addArchive(const Archive& archive) {
    if ( !contains(m_archives, archive) ) {
        m_archives.push_back(archive);
        mp_internalDb.reset();
    }
    return *this;
}

Search Searcher::search(const Query& query)
{
  if (!mp_internalDb) {
    initDatabase();
  }

  if (!mp_internalDb->hasDatabase()) {
    throw(std::runtime_error("Cannot create Search without FT Xapian index"));
  }

  return Search(mp_internalDb, query);
}

void Searcher::setVerbose(bool verbose)
{
  m_verbose = verbose;
}

void Searcher::initDatabase()
{
    mp_internalDb = std::make_shared<InternalDataBase>(m_archives, m_verbose);
}

namespace
{

// Match-all posting source that aborts the match once its flag is set.
// Combined with the real query via OP_FILTER so the flag is checked once per
// candidate document — including inside and-like positional checks, which is
// where an Enquire-level cancel would never get a chance to look.
class CancelPostingSource : public Xapian::PostingSource
{
  public:
    explicit CancelPostingSource(std::shared_ptr<std::atomic<bool>> cancelled)
      : mp_cancelled(std::move(cancelled))
    {}

    Xapian::doccount get_termfreq_min() const override { return m_doccount; }
    Xapian::doccount get_termfreq_est() const override { return m_doccount; }
    Xapian::doccount get_termfreq_max() const override { return m_doccount; }

    // Overriding init() rather than reset() keeps this buildable against both
    // Xapian 1.4 (init only) and 2.x (reset forwards to init).
    void init(const Xapian::Database& db) override
    {
      m_doccount = db.get_doccount();
      m_did = 0;
      m_atEnd = (m_doccount == 0);
    }

    void next(double) override
    {
      checkCancelled();
      if (m_atEnd) return;
      m_did = (m_did == 0) ? 1 : m_did + 1;
      if (m_did > m_doccount) m_atEnd = true;
    }

    void skip_to(Xapian::docid did, double) override
    {
      checkCancelled();
      if (m_atEnd) return;
      if (m_did < did) m_did = did;
      if (m_did > m_doccount) m_atEnd = true;
    }

    bool check(Xapian::docid did, double) override
    {
      checkCancelled();
      if (did > m_doccount) {
        m_atEnd = true;
        return false;
      }
      m_did = did;
      return true;
    }

    Xapian::docid get_docid() const override { return m_did; }

    bool at_end() const override { return m_atEnd; }

    Xapian::PostingSource* clone() const override
    {
      return new CancelPostingSource(mp_cancelled);
    }

    std::string get_description() const override
    {
      return "CancelPostingSource";
    }

  private:
    void checkCancelled() const
    {
      if (mp_cancelled->load(std::memory_order_relaxed))
        throw SearchCancelled();
    }

    std::shared_ptr<std::atomic<bool>> mp_cancelled;
    Xapian::docid m_did = 0;
    Xapian::doccount m_doccount = 0;
    bool m_atEnd = true;
};

} // anonymous namespace

// Everything Search gains for cancellation lives here, behind the one pointer
// slot Search already had, so sizeof(Search) does not change.
struct SearchState
{
    std::shared_ptr<std::atomic<bool>> cancelled
      = std::make_shared<std::atomic<bool>>(false);
    std::unique_ptr<Xapian::Enquire> enquire;
    // Query(PostingSource*) does not take ownership; keep the source alive.
    std::shared_ptr<Xapian::PostingSource> cancelSource;
};

Search::Search(std::shared_ptr<InternalDataBase> p_internalDb, const Query& query)
 : mp_internalDb(p_internalDb),
   mp_state(new SearchState),
   m_query(query)
{
}

Search::Search(Search&& s) = default;
Search& Search::operator=(Search&& s) = default;
Search::~Search() = default;

void Search::cancel()
{
    if (mp_state) {
        mp_state->cancelled->store(true, std::memory_order_relaxed);
    }
}

bool Search::isCancelled() const
{
    return mp_state && mp_state->cancelled->load(std::memory_order_relaxed);
}

Query::Query(const std::string& query) :
  m_query(query)
{}

Query& Query::setQuery(const std::string& query) {
    m_query = query;
    return *this;
}

Query& Query::setGeorange(float latitude, float longitude, float distance) {
    m_latitude = latitude;
    m_longitude = longitude;
    m_distance = distance;
    m_geoquery = true;
    return *this;
}

int Search::getEstimatedMatches() const
{
    LOCK_SEARCH(mp_internalDb);
    try {
      auto enquire = getEnquire();
      // Force xapian to check at least 10 documents even if we ask for an empty mset.
      // Else, the get_matches_estimated may be wrong and return 0 even if we have results.
      auto mset = enquire.get_mset(0, 0, 10);
      return mset.get_matches_estimated();
    } catch(const SearchCancelled&) {
      // Never fold a cancel into a search error.
      throw;
    } catch(Xapian::QueryParserError& e) {
      return 0;
    } catch(Xapian::DatabaseError& e) {
      throw zim::ZimFileFormatError(e.get_description());
    }
}

const SearchResultSet Search::getResults(int start, int maxResults) const {
    LOCK_SEARCH(mp_internalDb);
    try {
      auto enquire = getEnquire();
      auto mset = enquire.get_mset(start, maxResults);
      return SearchResultSet(mp_internalDb, std::move(mset));
    } catch(const SearchCancelled&) {
      // Never fold a cancel into a search error.
      throw;
    } catch(Xapian::QueryParserError& e) {
      return SearchResultSet(mp_internalDb);
    } catch(Xapian::DatabaseError& e) {
      throw zim::ZimFileFormatError(e.get_description());
    }
}

Xapian::Enquire& Search::getEnquire() const
{
    if ( mp_state->enquire ) {
        return *mp_state->enquire;
    }

    LOCK_SEARCH(mp_internalDb);
    auto enquire = std::unique_ptr<Xapian::Enquire>(new Xapian::Enquire(mp_internalDb->m_database));

    auto query = mp_internalDb->parseQuery(m_query);
    if (mp_internalDb->m_verbose) {
        std::cerr << "Parsed query '" << m_query.m_query << "' to " << query.get_description() << std::endl;
    }

    // Always installed: a match-all filter costs one atomic load per candidate
    // and leaves the result set and ranking untouched. Query(PostingSource*)
    // does not take ownership, so SearchState keeps the source alive.
    auto cancelSource = std::make_shared<CancelPostingSource>(mp_state->cancelled);
    query = Xapian::Query(Xapian::Query::OP_FILTER, query,
                          Xapian::Query(cancelSource.get()));
    mp_state->cancelSource = cancelSource;

    enquire->set_query(query);

    mp_state->enquire = std::move(enquire);
    return *mp_state->enquire;
}


SearchResultSet::SearchResultSet(std::shared_ptr<InternalDataBase> p_internalDb, Xapian::MSet&& mset) :
  mp_internalDb(p_internalDb),
  mp_mset(std::make_shared<Xapian::MSet>(mset))
{}

SearchResultSet::SearchResultSet(std::shared_ptr<InternalDataBase> p_internalDb) :
  mp_internalDb(p_internalDb),
  mp_mset(nullptr)
{}

int SearchResultSet::size() const
{
  if (! mp_mset) {
      return 0;
  }
  LOCK_SEARCH(mp_internalDb);
  try {
      return mp_mset->size();
  } catch(Xapian::DatabaseError& e) {
    throw zim::ZimFileFormatError(e.get_description());
  }
}

SearchResultSet::iterator SearchResultSet::begin() const
{
    if ( ! mp_mset ) {
        return nullptr;
    }
    LOCK_SEARCH(mp_internalDb);
    try {
        return new SearchIterator::InternalData(mp_internalDb, mp_mset, mp_mset->begin());
    } catch(Xapian::DatabaseError& e) {
        throw zim::ZimFileFormatError(e.get_description());
    }
}

SearchResultSet::iterator SearchResultSet::end() const
{
    if ( ! mp_mset ) {
        return nullptr;
    }
    LOCK_SEARCH(mp_internalDb);
    try {
        return new SearchIterator::InternalData(mp_internalDb, mp_mset, mp_mset->end());
    } catch(Xapian::DatabaseError& e) {
        throw zim::ZimFileFormatError(e.get_description());
    }
}

} //namespace zim
