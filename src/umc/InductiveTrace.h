#ifndef _INDUCTIVE_TRACE_
#define _INDUCTIVE_TRACE_

#include "UMC.h"
#include <boost/range/adaptor/map.hpp>
#include <boost/range/adaptor/indirected.hpp>

namespace UMC {
  // Forward declaration, as InductiveTrace needs to know about
  // ConsecutionChecker*
  class ConsecutionChecker;
  class CubeIndex;

  /*
   * Database to manage lemmas and fulfill the role of the inductive trace. The
   * Lemma structure stores the metadata about a lemma. This InductiveTrace
   * handles access to the data.
   *
   * Don't use this concurrently in multiple threads. The IDs are
   * auto-incremented in a non-threadsafe way.
   */
  class InductiveTrace {
    private:
      // Should be a map so references remain valid across operations
      // (not e.g., unordered_map)
      // InductiveTrace returns references into the map
      typedef std::map<CubeID, Lemma *> LemmaMap;

      std::unordered_map<Cube, CubeID> cube_to_id;
      std::unordered_map<CubeID, Cube> id_to_cube;
      std::vector<Frame> frames;
      Frame inf_frame;
      Frame empty_frame;
      CubeID last_id;
      std::list<Lemma> lemmas;
      LemmaMap active_lemmas;
      LemmaMap deleted_lemmas;
      std::unique_ptr<CubeIndex> cube_index;

      const UMCOptions & opts;
      UMCStats & stats;

      // The checkers are mutable because they are not coneptually part of the
      // inductive trace. The lemmas and their status are the conceptual state,
      // the chekcers are an implementation convenience
      mutable std::vector<ConsecutionChecker *> checkers;

      CubeID getNextID() {
        last_id++;
        return last_id;
      }

      const Lemma & addNewLemma(Lemma && lem);
      void growFrames(int size);
      Frame & getFrameAt(int index);
      const Frame & getFrameAt(int index) const;
      Lemma & getLemmaOf(const Cube & cube);
      Lemma & getLemmaOf(CubeID cube);

      // Functions to update the registered consecution checkers accordingly
      void lemmaAdded(const Lemma & lem);
      void lemmaModified(const Lemma & lem);
      void lemmaPromoted(const Lemma & lem);
      void lemmaDemoted(const Lemma & lem);
      void lemmaDeleted(const Lemma & lem);
      const Lemma & pushPull(const CubeID id, int level, bool pull = false);
    public:

      InductiveTrace(const UMCOptions & opts, UMCStats & stats);
      ~InductiveTrace();

      void clear();

      bool isActive(const Cube & cube) const;
      bool isActive(CubeID id) const;
      bool isDeleted(const Cube & cube) const;
      bool isDeleted(CubeID id) const;
      bool isKnown(const Cube & cube) const;
      bool isKnown(CubeID id) const;
      CubeID getID(const Cube & cube) const;
      const Cube & getCube(CubeID id) const;
      const Lemma & getLemma(const Cube & cube) const;
      const Lemma & getLemma(CubeID cube) const;
      const Lemma & getActiveLemma(const Cube & cube) const;
      const Lemma & getActiveLemma(CubeID cube) const;
      const Frame & getFrame(int index) const { return getFrameAt(index); }
      const Frame & getInfFrame() const { return getFrameAt(INT_MAX); }
      Frame copyFrame(int index) const { return getFrameAt(index); }
      Frame copyInfFrame() const { return copyFrame(INT_MAX); }
      int getMaxFrame() const { return frames.size() - 1; }

      const Lemma & addCube(const Cube & cube, int level);
      const Lemma & createLemma(const Cube & cube, int level);
      const Lemma & push(const CubeID id, int level);
      const Lemma & push(const Lemma & lem, int level);
      const Lemma & pull(const CubeID id, int level);
      const Lemma & pull(const Lemma & lem, int level);
      const Lemma & markBad(const Cube & cube, bool bad = true);
      const Lemma & markBad(CubeID id, bool bad = true);
      const Lemma & markUgly(const Cube & cube, bool ugly = true);
      const Lemma & markUgly(CubeID id, bool ugly = true);
      const Lemma & unmarkUgly(const Cube & cube) { return markUgly(cube, false); }
      const Lemma & unmarkUgly(const CubeID id) { return markUgly(id, false); }

      void deleteLemma(CubeID cube);
      void deleteLemma(const Lemma & lem);
      void silentlyDeleteLemma(CubeID cube);
      void silentlyDeleteLemma(const Lemma & lem);
      void deleteLemma(const Lemma & lem, bool inform_checkers);

      void registerConsecutionChecker(ConsecutionChecker & cons) const;
      void deregisterConsecutionChecker(ConsecutionChecker & cons) const;


      std::vector<CubeID> getCubesSubsumedBy(const Lemma & lemma) const;
      std::vector<CubeID> getCubesSubsumedByOld(const Lemma & lemma) const;

      decltype(active_lemmas | boost::adaptors::map_values | boost::adaptors::indirected)
      getActiveLemmas() {
        return active_lemmas | boost::adaptors::map_values | boost::adaptors::indirected;
      }

      decltype(const_cast<const LemmaMap&>(active_lemmas) | boost::adaptors::map_values | boost::adaptors::indirected)
      getActiveLemmas() const {
        return active_lemmas | boost::adaptors::map_values | boost::adaptors::indirected;
      }

      decltype(active_lemmas | boost::adaptors::map_values | boost::adaptors::indirected)
      getDeletedLemmas() {
        return deleted_lemmas | boost::adaptors::map_values | boost::adaptors::indirected;
      }

      decltype(const_cast<const LemmaMap&>(deleted_lemmas) | boost::adaptors::map_values | boost::adaptors::indirected)
      getDeletedLemmas() const {
        return deleted_lemmas | boost::adaptors::map_values | boost::adaptors::indirected;
      }
  };

}

#endif

