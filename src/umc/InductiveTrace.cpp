#include "InductiveTrace.h"
#include "Consecution.h"

namespace UMC {

  /*
   * CubeIndex provides an efficient interface to delete subsumed lemmas.
   * For each literal (either a state variable or its negation), the index
   * maintains a bucket that contains all CubeIDs referring to active lemmas
   * that contain the literal. Given a cube c, it's relatively efficient to
   * find all the other cubes that are subsumed by c by intersecting the
   * buckets for each literal in c.
   *
   * The IC3 tactic has a similar implementation in a class called
   * SubsumptionUniverse, but it's slightly incomprehensible.
   */
  class CubeIndex {
    public:
      CubeIndex() { }

      void add(CubeID cube_id, const Cube & cube);
      void remove(CubeID cube_id, const Cube & cube);
      void clear();

      std::vector<CubeID> subsumedCubes(const Cube & cube) const;

    private:
      void addToBucket(ID id, CubeID cube_id);
      typedef std::set<CubeID> CubeBucket;
      typedef std::unordered_map<ID, CubeBucket> BucketStorage;
      BucketStorage buckets;
  };

  void CubeIndex::addToBucket(ID id, CubeID cube_id) {
    auto it = buckets.find(id);
    if (it == buckets.end()) {
      auto insert_result = buckets.insert(std::make_pair(id, CubeBucket()));
      it = insert_result.first;
      assert(insert_result.second);
    }
    assert(it != buckets.end());

    CubeBucket & bucket = it->second;
    bucket.insert(cube_id);
  }

  void CubeIndex::add(CubeID cube_id, const Cube & cube) {
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif

    for (ID id : cube) {
      addToBucket(id, cube_id);
    }
  }

  void CubeIndex::remove(CubeID cube_id, const Cube & cube) {
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
    for (ID id : cube) {
      auto it = buckets.find(id);
      assert(it != buckets.end());
      const CubeBucket & bucket = it->second;
      assert(bucket.find(cube_id) != bucket.end());
    }

    for (auto pair : buckets) {
      ID id = pair.first;
      const CubeBucket & bucket = pair.second;
      // Check that the cube_id is or is not present in the bucket
      // as appropriate
      if (std::find(cube.begin(), cube.end(), id) == cube.end()) {
        assert(bucket.find(cube_id) == bucket.end());
      } else {
        assert(bucket.find(cube_id) != bucket.end());
      }
    }
#endif

    for (ID id : cube) {
      auto it = buckets.find(id);
      assert(it != buckets.end());
      CubeBucket & bucket = it->second;
      bucket.erase(cube_id);
    }
  }

  std::vector<CubeID> CubeIndex::subsumedCubes(const Cube & cube) const {
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
    assert(!cube.empty());
#endif
    std::vector<CubeID> subsumed_cubes;
    for (ID id : cube) {
      auto it = buckets.find(id);
      if (it != buckets.end()) {
        const CubeBucket & bucket = it->second;
        if (subsumed_cubes.empty()) {
          // The first run through, so initialized the vector
          subsumed_cubes.insert(subsumed_cubes.end(), bucket.begin(), bucket.end());
        } else {
          // Otherwise intersect it with the bucket
          std::vector<ID> tmp;
          std::set_intersection(subsumed_cubes.begin(), subsumed_cubes.end(),
                                bucket.begin(), bucket.end(),
                                std::back_inserter(tmp));
          subsumed_cubes = tmp;
          // If the intersection is empty, we're done
          if (tmp.empty()) {
            break;
          }
        }
      } else {
        // If there is no bucket, no other cubes contain this literal
        subsumed_cubes.clear();
        break;
      }
    }

    return subsumed_cubes;
  }

  void CubeIndex::clear() {
    buckets.clear();
  }

  InductiveTrace::InductiveTrace(const UMCOptions & opts,
                                 UMCStats & stats) :
                                     last_id(CUBE_ID_NULL),
                                     cube_index(new CubeIndex()),
                                     opts(opts),
                                     stats(stats)
  { }

  /*
   * This destructor is defined here because we use unique_ptr<CubeIndex>, and
   * CubeIndex is incomplete in the header file. It won't compile unless the
   * destructor is defined after CubeIndex is complete.
   */
  InductiveTrace::~InductiveTrace() { }

  /*
   * Get all cubes subsumed by the given cube.
   */
  std::vector<CubeID> InductiveTrace::getCubesSubsumedBy(const Lemma & lem) const {
    std::vector<CubeID> all_subsumed = cube_index->subsumedCubes(lem.getCube());
    std::vector<CubeID> subsumed;

    // Filter out based on level
    for (CubeID id : all_subsumed) {
      const Lemma & sublem = getLemma(id);
      if (sublem.level <= lem.level) {
        subsumed.push_back(sublem.getID());
      }
    }

    return subsumed;
  }

  /*
   * Clear the inductive trace, reseting it to a pristine state
   */
  void InductiveTrace::clear() {
    cube_to_id.clear();
    id_to_cube.clear();
    frames.clear();
    active_lemmas.clear();
    deleted_lemmas.clear();
    lemmas.clear();
    cube_index->clear();
    last_id = CUBE_ID_NULL;
  }

  /*
   * Add a new lemma to the inductive trace with the ID returned by GetID(),
   * which must not be already known. Return a reference to the new lemma. The
   * argument lemma is no longer usable.
   */
  const Lemma & InductiveTrace::addNewLemma(Lemma && lem) {
    CubeID id = lem.getID();
    const Cube & cube = lem.getCube();
    assert(cube_to_id.find(cube) == cube_to_id.end());
    assert(id_to_cube.find(id) == id_to_cube.end());
    cube_to_id[cube] = id;
    id_to_cube[id] = cube;

    assert(active_lemmas.find(id) == active_lemmas.end());

    lemmas.emplace_back(std::move(lem));
    Lemma & stored = lemmas.back();
    active_lemmas[id] = &stored;

    return stored;
  }

  /*
   * Grow the frames structure. This could invalidate any references into
   * frames.
   */
  void InductiveTrace::growFrames(int max_level) {
    assert(max_level < INT_MAX);
    int size = max_level + 1;
    if (frames.size() < (size_t) size) {
      frames.resize(size);
    }
  }

  /*
   * Return a reference to the given frame. Note: references may be invalidated
   * by calls to growFrames
   */
  const Frame & InductiveTrace::getFrameAt(int index) const {
    if (index == INT_MAX) {
      return inf_frame;
    } else if ((size_t) index < frames.size()) {
      return frames.at(index);
    } else {
      assert(empty_frame.empty());
      return empty_frame;
    }
  }

  Frame & InductiveTrace::getFrameAt(int index) {
    // Avoid duplicating code between const and non-const versions
    return const_cast<Frame &>(static_cast<const InductiveTrace &>(*this).getFrameAt(index));
  }

  /*
   * Returns whether or not the given cube is known (has an ID)
   */
  bool InductiveTrace::isKnown(const Cube & cube) const {
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif
    bool res = (cube_to_id.find(cube) != cube_to_id.end());
#ifdef DEBUG
    if (res) {
      CubeID id = cube_to_id.at(cube);
      assert(id_to_cube.at(id) == cube);
    }
#endif
    return res;
  }

  bool InductiveTrace::isKnown(CubeID id) const {
    bool res = id_to_cube.find(id) != id_to_cube.end();
#ifdef DEBUG
    if (res) {
      const Cube & cube = id_to_cube.at(id);
      assert(cube_to_id.at(cube) == id);
    }
#endif
    return res;
  }

  /*
   *  Returns whether or not the given cube is active (known and not deleted)
   */
  bool InductiveTrace::isActive(const Cube & cube) const {
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif
    if (!isKnown(cube)) { return false; }
    CubeID id = getID(cube);
    return isActive(id);
  }

  bool InductiveTrace::isActive(CubeID id) const {
    if (!isKnown(id)) { return false; }
    bool res = active_lemmas.find(id) != active_lemmas.end();
#ifdef DEBUG
    if (res) {
      const Lemma & lem = *active_lemmas.at(id);
      assert(lem.getID() == id);
    }
#endif
    return res;
  }

  /*
   *  Returns whether or not the given cube is deleted
   */
  bool InductiveTrace::isDeleted(const Cube & cube) const {
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif
    if (!isKnown(cube)) { return false; }
    CubeID id = getID(cube);
    return isDeleted(id);
  }

  bool InductiveTrace::isDeleted(CubeID id) const {
    if (!isKnown(id)) { return false; }
    bool res = deleted_lemmas.find(id) != deleted_lemmas.end();
#ifdef DEBUG
    if (res) {
      const Lemma & lem = *deleted_lemmas.at(id);
      assert(lem.getID() == id);
    }
#endif
    return res;
  }

  /*
   * Add the new cube as a lemma at level, whatever that means (push it
   * forward, create a new lemma, revive a deleted lemma, etc.).
   * If the lemma is already present at level or higher, nothing happens.
   * Returns a const reference to the lemma.
   */
  const Lemma & InductiveTrace::addCube(const Cube & cube, int level) {
    assert(!cube.empty());
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif

    if (isActive(cube)) {
      assert(!isDeleted(cube));
      // Find
      const Lemma & lem = getActiveLemma(cube);
      int prev_level = lem.level;
      if (prev_level < level) {
        // Update
        const Lemma & lem_pushed = push(lem, level);
        return lem_pushed;
      }
      return lem;
    } else {
      // Initialize. If cube has been deleted previously, createLemma properly
      // handles things
      const Lemma & lem = createLemma(cube, level);
      return lem;
    }
  }

  /*
   * Creates a new lemma for the given cube. If the lemma has been previously
   * deleted, it will be revived. Returns a const reference to the new lemma.
   */
  const Lemma & InductiveTrace::createLemma(const Cube & cube, int level) {
    Cube cube_sorted = cube;
    std::sort(cube_sorted.begin(), cube_sorted.end());

    if (level < INT_MAX) {
      growFrames(level);
    }

    const Lemma * canonical = nullptr;

    if (isKnown(cube_sorted)) {
      CubeID id = getID(cube_sorted);
      assert(isDeleted(id));
      assert(!isActive(id));

      auto it = deleted_lemmas.find(id);
      assert(it != deleted_lemmas.end());
      Lemma * deleted = it->second;
      deleted_lemmas.erase(it);

      assert(active_lemmas.find(id) == active_lemmas.end());
      active_lemmas.insert(std::make_pair(id, deleted));
      deleted->level = level;

      canonical = deleted;
    } else {
      canonical = &(addNewLemma(Lemma(cube_sorted, getNextID(), level)));
    }

    assert(canonical);
    CubeID id = canonical->getID();
    assert(canonical->level == level);

    Frame & frame = getFrameAt(level);
    frame.insert(id);

    if (opts.subsumption_reduce) {
      AutoTimer timer(stats.reduce_frames_time);
      cube_index->add(id, canonical->getCube());
    }
    lemmaAdded(*canonical);

    return *canonical;
  }

  /* Returns the ID of the given cube, which must be already known */
  CubeID InductiveTrace::getID(const Cube & cube) const {
    assert(isKnown(cube));

    return cube_to_id.at(cube);
  }

  /* Returns the cube with the given ID, which must be assigned already */
  const Cube & InductiveTrace::getCube(CubeID id) const {
    assert(isKnown(id));

    return id_to_cube.at(id);
  }

  Lemma & InductiveTrace::getLemmaOf(const Cube & cube) {
    // This calls the const version and cast away the const-ness.
    // It seems wrong, but avoids duplicating the exact same code
    // between the const and non-const versions
    return const_cast<Lemma &>(static_cast<const InductiveTrace &>(*this).getLemma(cube));
  }

  Lemma & InductiveTrace::getLemmaOf(CubeID id) {
    return const_cast<Lemma &>(static_cast<const InductiveTrace &>(*this).getLemma(id));
}

  const Lemma & InductiveTrace::getLemma(const Cube & cube) const {
    assert(isKnown(cube));
    CubeID id = getID(cube);
    return getLemma(id);
  }

  const Lemma & InductiveTrace::getLemma(CubeID id) const {
    assert(isKnown(id));
    auto active_it = active_lemmas.find(id);
    if (active_it == active_lemmas.end()) {
      auto deleted_it = deleted_lemmas.find(id);
      assert(deleted_it != deleted_lemmas.end());
      return *deleted_it->second;
    } else {
#ifdef DEBUG
      assert(deleted_lemmas.find(id) == deleted_lemmas.end());
#endif
      return *active_it->second;
    }
  }

  const Lemma & InductiveTrace::getActiveLemma(const Cube & cube) const {
    assert(isActive(cube));
    return getLemma(cube);
  }

  const Lemma & InductiveTrace::getActiveLemma(CubeID id) const {
    assert(isActive(id));
    return getLemma(id);
  }

  void InductiveTrace::silentlyDeleteLemma(CubeID id) {
    assert(isActive(id));
    const Lemma & lem = getActiveLemma(id);
    silentlyDeleteLemma(lem);
  }

  /*
   * Delete a lemma from the trace. Its CubeID stops being valid at this point.
   * The lemma is deleted silently; that is, the consecution checkers are not
   * informed of its deletion. This shoul be used to delete lemmas that are
   * subsumed by other existing lemmas.
   */
  void InductiveTrace::silentlyDeleteLemma(const Lemma & lem) {
    deleteLemma(lem, false);
  }

  void InductiveTrace::deleteLemma(CubeID id) {
    assert(isActive(id));
    const Lemma & lem = getActiveLemma(id);
    deleteLemma(lem);
  }

  void InductiveTrace::deleteLemma(const Lemma & lem) {
    deleteLemma(lem, true);
  }

  /*
   * Delete a lemma from the trace. Its CubeID stops being valid at this point.
   */
  void InductiveTrace::deleteLemma(const Lemma & lem, bool inform_checkers) {
    CubeID id = lem.getID();
    assert(isActive(id));
    int level = lem.level;

    // Call this here, because we will eventually remove the lemma from the
    // container holding it and anyone trying to access it will fail
    if (opts.subsumption_reduce) {
      AutoTimer timer(stats.reduce_frames_time);
      cube_index->remove(id, lem.getCube());
    }
    if (inform_checkers) { lemmaDeleted(lem); }

    auto lem_it = active_lemmas.find(id);
    assert(lem_it != active_lemmas.end());
    Lemma * canonical = lem_it->second;
    // Assert the reference is a pointer to the canonical copy of the lemma
    assert(canonical == &lem);
    active_lemmas.erase(lem_it);

    Frame & fk = getFrameAt(level);
    bool found = false;
    for (auto it = fk.begin(); it != fk.end(); ++it) {
      if (*it == id) {
        fk.erase(it);
        found = true;
        break;
      }
    }

    assert(found);

    assert(deleted_lemmas.find(id) == deleted_lemmas.end());
    deleted_lemmas[id] = canonical;
    canonical->level = -1;
  }

  /*
   * Pushes the lemma with the given ID forward (or backward) to level
   */
  const Lemma & InductiveTrace::pushPull(CubeID id, int level, bool pull) {
    assert(isActive(id));
    if (level < INT_MAX) {
      growFrames(level);
    }

    Lemma & lem = getLemmaOf(id);
    int old_level = lem.level;

    if (pull) {
      assert(old_level >= lem.level);
    } else {
      assert(old_level <= lem.level);
    }

    Frame & old_frame = getFrameAt(old_level);
    Frame & new_frame = getFrameAt(level);

    assert(old_frame.find(id) != old_frame.end());

    bool updated = level != lem.level;
    if (updated) {
      old_frame.erase(id);
      new_frame.insert(id);
      lem.level = level;
      if (lem.level < old_level) {
        // Some consecution checkers can't handle lemmas being removed from
        // F_inf and there is probably no reason to do so anyway
        assert(old_level != INT_MAX);
        lemmaDemoted(lem);
      } else {
        lemmaPromoted(lem);
      }
    }

    return lem;
  }

  const Lemma & InductiveTrace::push(CubeID id, int level) {
    return pushPull(id, level, false);
  }

  const Lemma & InductiveTrace::push(const Lemma & lem, int level) {
    CubeID id = lem.getID();
    return push(id, level);
  }

  const Lemma & InductiveTrace::pull(CubeID id, int level) {
    return pushPull(id, level, true);
  }

  const Lemma & InductiveTrace::pull(const Lemma & lem, int level) {
    CubeID id = lem.getID();
    return pull(id, level);
  }


  const Lemma & InductiveTrace::markBad(const Cube & cube, bool bad) {
    assert(isKnown(cube));
    CubeID id = getID(cube);
    return markBad(id, bad);
  }

  const Lemma & InductiveTrace::markBad(CubeID id, bool bad) {
    Lemma & lem = getLemmaOf(id);
    // If there ever is a reason to unmark a lemma as bad, this assert can be
    // removed. For now, logically it makes no sense so we'll check
    assert(bad);

    bool active = isActive(id);
    bool updated = !lem.bad;
    lem.bad = bad;

    if (active && updated) { lemmaModified(lem); }

    return lem;
  }

  const Lemma & InductiveTrace::markUgly(const Cube & cube, bool ugly) {
    assert(isKnown(cube));
    CubeID id = getID(cube);
    return markUgly(id, ugly);
  }

  const Lemma & InductiveTrace::markUgly(CubeID id, bool ugly) {
    Lemma & lem = getLemmaOf(id);

    bool active = isActive(id);
    bool updated = lem.ugly != ugly;
    lem.ugly = ugly;

    if (active && updated) { lemmaModified(lem); }

    return lem;
  }

  void InductiveTrace::registerConsecutionChecker(ConsecutionChecker & cons) const {
    checkers.push_back(&cons);
  }

  void InductiveTrace::deregisterConsecutionChecker(ConsecutionChecker & cons) const {
    auto it = std::find(checkers.begin(), checkers.end(), &cons);
    if (it != checkers.end()) {
      checkers.erase(it);
    }
  }

  void InductiveTrace::lemmaAdded(const Lemma & lem) {
    CubeID id = lem.getID();
    for (ConsecutionChecker * checker : checkers) {
      checker->lemmaAdded(id);
    }
  }

  void InductiveTrace::lemmaModified(const Lemma & lem) {
    CubeID id = lem.getID();
    for (ConsecutionChecker * checker : checkers) {
      checker->lemmaModified(id);
    }
  }

  void InductiveTrace::lemmaPromoted(const Lemma & lem) {
    CubeID id = lem.getID();
    for (ConsecutionChecker * checker : checkers) {
      checker->lemmaPromoted(id);
    }
  }

  void InductiveTrace::lemmaDemoted(const Lemma & lem) {
    CubeID id = lem.getID();
    for (ConsecutionChecker * checker : checkers) {
      checker->lemmaDemoted(id);
    }
  }

  void InductiveTrace::lemmaDeleted(const Lemma & lem) {
    CubeID id = lem.getID();
    for (ConsecutionChecker * checker : checkers) {
      checker->lemmaDeleted(id);
    }
  }

}

