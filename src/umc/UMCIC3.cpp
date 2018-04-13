#include "UMCIC3.h"

namespace UMC {
  IC3Solver::IC3Solver(Model & m, UMCOptions o) :
    UMCEngine(m, o),
    cons_checker  (checkerFromString(o.primary_cons)),
    init_checker  (checker<InitialChecker>(initCube())),
    lifter        (checker<UNSATCoreLifter>()),
    gen           (generalizer<Generalizer>(*cons_checker))
  {
    ic3Prepare();
  }

  void IC3Solver::cleanup() {
    UMCEngine::cleanup();
    ic3Cleanup();
  }

  void IC3Solver::ic3Cleanup() { }

  void IC3Solver::prepare(UMCOptions * new_opts) {
    UMCEngine::prepare(new_opts);
    ic3Prepare();
  }

  void IC3Solver::ic3Prepare() {
    bool trivial = ic3RenewSAT();
    assert(!trivial);
  }

  bool IC3Solver::renewSAT() {
    return ic3RenewSAT();
  }

  bool IC3Solver::ic3RenewSAT() {
    logger.verbose() << "renewSAT" << std::endl;

    bool trivial = cons_checker->renewSAT();
    trivial = trivial || lifter->renewSAT();
    trivial = trivial || init_checker->renewSAT();

    return trivial;
  }

  void IC3Solver::renew() {
    bool trivial = renewSAT();
    assert(!trivial);
  }

  bool IC3Solver::checkInitial(const Cube & bad_cube) const
  {
    ConsecutionOpts copts;
    copts.unprimed_cube = &bad_cube;
    return !init_checker->consecution(copts);
  }

  bool IC3Solver::checkInf(const Cube & bad_cube) const
  {
    (void) bad_cube;
    return false;
  }

  bool IC3Solver::proofFound() {
    for (size_t i = getLevel(); i >= 1; --i) {
      if (inductive_trace.getFrame(i).empty()) {
        return true;
      }
    }
    return false;
  }

  bool IC3Solver::consecution(const Cube & c,
                               int k,
                               SAT::Assignment * asgn,
                               Cube * reduced) {
    stats.consecution_calls++;
    ConsecutionOpts copts;
    copts.level = k;
    copts.cube = &c;
    copts.assignment = asgn;
    copts.reduced = reduced;

    return cons_checker->consecution(copts);
  }

  int IC3Solver::generalize(int lo, int hi, Cube & cube) {
    return gen->generalize(lo, hi, cube);
  }

  void IC3Solver::lift(Cube & t,
                        const Cube & inputs,
                        const Cube & p_inputs,
                        const Cube & s) const
  {
    lifter->lift(t, inputs, p_inputs, s);
  }

  /*
   * IC3-style pushing
   */
  void IC3Solver::pushClauses()
  {
    logger.verbose() << "\nStarting pushClauses" << std::endl;
    AutoTimer auto_timer(stats.push_time);

    for (int k = 1; k <= getLevel(); k++) {
      int push_count = 0;

      const Frame fk = inductive_trace.copyFrame(k);
      int fk_size = fk.size();
      for (auto it = fk.begin(); it != fk.end(); ++it) {
        const Lemma & lem = getActiveLemma(*it);
        assert(lem.level >= k);

        // It might've been pushed earlier as a sside effect of reducing
        // another lemma
        if (lem.level > k) {
          push_count++;
          continue;
        }

        Cube reduced;
        int result = tryPropagate(lem, reduced);
        assert(result >= k);
        assert(result <= (getLevel() + 1) || result == INT_MAX);
        if (result > k) {
          push_count++;
          lemmaPushed(lem, result, reduced);
        }
      }

      if (push_count == fk_size) {
        assert(inductive_trace.getFrame(k).empty());
        logger.logorrheic() << "Found proof at k = " << k << std::endl;
        // Put the proof into F_inf
        Frame inductive_frame;
        for (int i = k + 1; i <= inductive_trace.getMaxFrame(); i++) {
          const Frame & fi = inductive_trace.getFrame(i);
          inductive_frame.insert(fi.begin(), fi.end());
        }

        for(auto it = inductive_frame.begin(); it != inductive_frame.end(); ++it) {
          addCubeByID(*it, INT_MAX);
        }

#ifdef DEBUG
        for (int i = k; i <= inductive_trace.getMaxFrame(); i++) {
          assert(inductive_trace.getFrame(i).empty());
        }
        assert(consecution(badCube(), INT_MAX));
#endif

        break;
      }
    }
  }

}

