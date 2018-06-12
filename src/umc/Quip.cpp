/********************************************************************
Copyright (c) 2010-2015, Regents of the University of Colorado

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

Neither the name of the University of Colorado nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
********************************************************************/

#include "Quip.h"
#include <queue>
#include <sstream>
#include <boost/algorithm/string.hpp>
#include <algorithm>

namespace UMC {

  /*
   * Create and add a new reachable state. If the state is already an active
   * state, simply return the pre-existing one
   */
  ReachableState * ReachableStateManager::addState(const Cube & cube, const Cube & inputs)
  {
    AutoTimer auto_timer(stats.states_time);
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif
    stats.total_states++;
    // Check if the new state already exists in the active portion of the list
    size_t count = 0;
    for (ReachableState * r : states) {
      count++;
      if (r->state == cube) {
        return r;
      }

      if (count >= maxn_states) {
        break;
      }
    }

    stats.unique_states++;
    ReachableState * new_state = new ReachableState(cube, inputs);
    states.push_front(new_state);

    return new_state;
  }

  /*
   * Return first (most active) reachable state which intersects with cube, or
   * NULL if no state active state intersects with cube.
   * Automatically promote the intersecting state to the front of the list.
   * Note: we can never remove states since we might need them to build
   * counter-example traces. So only the first N states are considered active.
   */
  ReachableState * ReachableStateManager::intersect(const Cube & cube)
  {
    AutoTimer auto_timer(stats.states_time);
#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
#endif
    size_t count = 0;
    for (auto it = states.begin();
         it != states.end() && count < maxn_states;
         it++, count++) {
      ReachableState * r = *it;
      if (subsumes(r->state, cube)) {
        // Move the identified state to the front
        states.erase(it);
        states.push_front(r);
        stats.state_matches++;
        return r;
      }
    }
    return NULL;
  }

  ConsecutionChecker * QuipSolver::constructExclChecker() const {
    if (options().excl_type == ACTIVATION) {
     return checker<ActivationBasedConsecutionChecker>();
    } else if (options().excl_type == LAZY) {
     return checker<MultiSATConsecutionChecker>();
    } else if (options().excl_type == MULTI) {
      return checker<ActivationMultiSATConsecutionChecker>();
    } else {
      assert(false);
    }
  }

  /*
   * Note: init_checker uses the (transient) initCube(), the others use
   * trueInitCube(). This allows us to generate lemmas that satisfy
   * initiation with respect to the true initial states (for incrementality)
   * while still supporting queries that start at arbitrary reachable states
   */
  QuipSolver::QuipSolver(Model & m, UMCOptions o) :
    UMCEngine(m, o),
    cons_checker  (checkerFromString(o.primary_cons)),
    inf_checker   (checker<InfChecker>()),
    init_checker  (checker<InitialChecker>(initCube())),
    excl_checker  (options().excl_gen || options().excl_push ? constructExclChecker() : nullptr),
    lifter        (checker<UNSATCoreLifter>()),
    gen           (generalizerFromString(o.gen, *cons_checker)),
    excl_gen      (options().excl_gen ? generalizerFromString(o.gen, *excl_checker) : nullptr),
    rsman(stats, o.max_reachable_states)
  {
    quipPrepare();
  }

  /*
   * Cleanup function for things that should be cleaned up between incremental
   * runs.  Things that should persist across incremental runs should be
   * cleared in the destructor
   */
  void QuipSolver::cleanup() {
    UMCEngine::cleanup();
    quipCleanup();
  }

  void QuipSolver::quipCleanup() {
    rsman.clear();
  }

  /*
   * Prepare function to set up things that are unique to a particular
   * incremental run.  Things that last across incremental runs should be set
   * up in the constructor.
   */
  void QuipSolver::prepare(UMCOptions * new_opts) {
    UMCEngine::prepare(new_opts);
    quipPrepare();
  }

  void QuipSolver::quipPrepare() {
    if (excl_checker) {
      if (options().excl_type == LAZY) {
        excl_checker->setLazyFilter(no_bad_no_ugly);
      } else {
        excl_checker->setStrongFilter(no_bad_no_ugly);
      }
    }

    bool trivial = quipRenewSAT();
    assert(!trivial);

    rsman.setMaxStates(options().max_reachable_states);
    rsman.addState(initCube(), Cube());
  }

  void QuipSolver::markBad(const Cube & cube) {
    assert(isKnownLemma(cube));
    inductive_trace.markBad(cube);
  }

  void QuipSolver::onAddKnownCube(const Lemma & lem, int lv) {
    (void) lv;
    if (lem.bad) {
      stats.bad_lemmas_relearned++;
    }
  }

  /*
   * Check for the case where bad_cube intersects the initial conditions.
   */
  bool QuipSolver::checkInitial(const Cube & bad_cube) const
  {
    ConsecutionOpts copts;
    copts.unprimed_cube = &bad_cube;
    return !init_checker->consecution(copts);
  }

  /*
   * Check if bad_cube intersects with F_inf
   */
  bool QuipSolver::checkInf(const Cube & bad_cube) const
  {
    //do sat query F_0 ^ bad
    ConsecutionOpts copts;
    copts.unprimed_cube = &bad_cube;
    return !inf_checker->consecution(copts);
  }

  bool QuipSolver::consecution(const Cube & c,
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

  /*
   * Generalize the given cube by removing literals while maintaining inductiveness
   * lo - lowest level to consider
   * hi - highest level to consider
   */
  int QuipSolver::generalize(int lo, int hi, Cube & cube) {
    Generalizer * generalizer = gen.get();
    if (options().excl_gen) {
      assert(excl_gen);
      assert(excl_checker);

      stats.consecution_calls++;

      if (excl_checker->consecution(cube, lo)) {
        generalizer = excl_gen.get();
      }
    }
    return generalizer->generalize(lo, hi, cube);
  }

  /*
   * UNSAT core lifting to generalize predecessor states
   * t - predecessor cube
   * inputs - values of input variables which lead to s
   * p_inputs - values of primed input variables which may be implied by s
   */
  void QuipSolver::lift(Cube & t,
                        const Cube & inputs,
                        const Cube & p_inputs,
                        const Cube & s) const
  {
    lifter->lift(t, inputs, p_inputs, s);
  }

  /*
   * Return a state (cube) r such that r is 1-step reachable from r0 and
   * intersects the parent cube of po.
   */
  ReachableState * QuipSolver::extractReachable(ProofObligation & po, const Cube & r0)
  {
    // "Simulate" the transition r0->r with the sat query r0 & T & inputs & r',
    // where r' is a cube of all the state variables. All variables in the
    // formula are assigned in the assumptions except the literals not in
    // po->parent.
    assert(po.parent != NULL);

    SAT::Assignment asgn;
    // interested in all the primed state variables
    Expr::IDVector state_vars(stateVars().begin(), stateVars().end());
    prime(state_vars);
    for (ID id : state_vars) {
      asgn.insert(SAT::Assignment::value_type(id, SAT::Unknown));
    }

    // Assume po->parent->cube (primed) - we can't use copts.cube because it
    // will be added on both sides of the trasition relation;
    Expr::IDVector assumps = po.parent->cube;
    prime(assumps);
    // Assume the inputs
    assumps.insert(assumps.end(), po.inputs.begin(), po.inputs.end());

    stats.sat_calls++;
    ConsecutionOpts copts;
    copts.unprimed_cube = &r0;
    copts.extra_assumps = &assumps;
    copts.assignment = &asgn;
    copts.level = INT_MAX;
    bool cons = inf_checker->consecution(copts);
    assert(!cons);

    Cube r;
    for (auto it = asgn.begin(); it != asgn.end(); it++) {
      assert(it->second != SAT::Unknown);
      ID assigned = it->first;
      ID nassigned = ev->apply(Expr::Not, assigned);
      ID unprimed = ev->unprime(it->second == SAT::False ? nassigned : assigned);
      r.push_back(unprimed);
    }
    std::sort(r.begin(), r.end());

    {
      AutoTimer auto_timer(stats.states_time);
      // Mark all cubes excluding r as bad
      for (Lemma & lem : inductive_trace.getActiveLemmas()) {
        const Cube & cube = lem.getCube();
        if (cube != badCube() && !lem.bad && subsumes(r, cube)) {
          logger.logorrheic() << "Marking as bad " << pc(cube) << std::endl;
          // Good lemmas (at infinity) can't be bad
          assert(lem.level < INT_MAX);
          markBad(cube);
        }
      }
    }

    ReachableState * rs = rsman.addState(r, po.inputs);
    return rs;
  }

  /*
   * Handle a failed may proof obligation. Extract and store the trace, and mark
   * the obligations in the chain as failed. Returns a ReachableState * for the
   * first reachable state in the trace.
   */
  ReachableState * QuipSolver::handleFailedMayProof(ProofObligation & po, const Cube & pred) {
    assert(po.type == MAY_PROOF);

    ReachableState * r0 = extractReachable(po, pred);

    // Go up through the chain of obligations and mark them as failed.
    // Otherwise, we may end up in a situation where we drop the
    // reachable state we just learned (or if max_reachable_states is 0,
    // never store it) and therefore reconsider this obligation repeatedly

    if (isKnownLemma(po.cube)) {
      markBad(po.cube);
    }

    ProofObligation * obl = po.parent;
    ReachableState * r = r0;
    while (obl) {
      assert(obl->type == MAY_PROOF);
      obl->failed = true;
      stats.may_fail++;

      if (isKnownLemma(obl->cube)) {
        markBad(obl->cube);
      }

      if (obl->parent) {
        ReachableState * r_new = extractReachable(*obl, r->state);
        r_new->pre = r;
        r = r_new;
      }
      obl = obl->parent;
    }

    return r0;
  }

  std::pair<bool, bool> QuipSolver::beforeBlock(ProofObligation & po) {
    // Counter-example found the old-fashioned way
    // (proof obligations going back to 0)
    if (po.level == 0) {
      if (po.type == MUST_PROOF) {
        po.cex_state = initCube();
        return std::make_pair(true, true);
      } else {
        // Handle the failure, generating a trace of reachable states starting
        // from the initial state
        stats.may_fail++;
        handleFailedMayProof(po, initCube());
        return std::make_pair(true, false);
      }
    }

    ReachableState * r0 = rsman.intersect(po.cube);
    // Counter-example found via reachable states
    if (r0) {
      logger.logorrheic() << "Cube intersects reachable state "
                          << pc(r0->state)
                          << std::endl;
      if (po.type == MUST_PROOF) {
        // buildCex ignores r0's state, so we can use it in po
        po.cex_state = r0->state;
        return std::make_pair(true, true);
      }
      else {
        assert(po.type == MAY_PROOF);
        if (po.parent == NULL) {
          // Just mark the cube as bad if it's a known lemma
          if (isKnownLemma(po.cube)) {
            assert(isActiveLemma(po.cube));
            markBad(po.cube);
          }
        } else {
          // Since po->cube is known reachable, generate a trace starting from
          // r0->state.
          ReachableState * r = handleFailedMayProof(po, r0->state);
          r->pre = r0;
        }
        stats.may_fail++;
        return std::make_pair(true, false);
      }
    }
    return std::make_pair(false, false);
  }

  void QuipSolver::onDischarge(ProofObligation & po, const Cube & t, int g) {
    //po->cube is blocked by !t
    if (po.type == MAY_PROOF) {
      stats.may_success++;
    } else {
      stats.must_success++;
    }

    if (g < INT_MAX && (g + 1) < getLevel()) {
      po.level = g + 1;
      // Optionally re-enqueue a must-proof obligation for the original CTI,
      // IC3-style
      if (po.type == MUST_PROOF && options().reenqueue_both) {
        ProofObligation & copy = copyObligation(po);
        pushObligation(copy);
      }

      // Re-add obligation for t, Quip-style
      if (t != po.cube) {
        po.type = MAY_PROOF;
        po.parent = NULL;
        po.cube = t;
        pushObligation(po);
      }
    }
  }

  void QuipSolver::onRenew() {
    bool trivial = renewSAT();
    assert(!trivial);
  }

  bool QuipSolver::beforeTryPropagate(const Lemma & lem) {
    return !lem.bad;
  }

  void QuipSolver::lemmaPushed(const Lemma & lem, int level, const Cube & reduced) {
    const Cube & c = lem.getCube();
    assert(reduced.size() <= c.size());
#ifdef DEBUG
    Cube copy = reduced;
    std::sort(copy.begin(), copy.end());
    assert(subsumes(c, copy));
    assert(level > 0);
    assert(consecution(c, level - (level == INT_MAX ? 0 : 1)));
    assert(consecution(reduced, level - (level == INT_MAX ? 0 : 1)));
#endif
    addCube(c, level);
    if (options().reduce_frames && reduced.size() < c.size()) {
      if (isDeletedLemma(reduced) || isActiveLemma(reduced)) {
        const Lemma & red_lem = getLemma(reduced);
        if (!red_lem.bad && red_lem.level >= level) {
          addCube(reduced, level);
          deleteSubsumedLemma(lem);
        }
      } else {
        addCube(reduced, level);
        deleteSubsumedLemma(lem);
      }
    }
  }

  void QuipSolver::reduceFrames() {
    AutoTimer timer(stats.reduce_frames_time);
    for (int i = inductive_trace.getMaxFrame(); i >= 0; --i) {
      Frame fi = inductive_trace.copyFrame(i);
      for (CubeID id : fi) {
        if (isActiveLemma(id)) {
          const Lemma & lem = getActiveLemma(id);
          if (!lem.bad && !lem.ugly) {
            deleteAllSubsumedBy(lem);
          }
        }
      }
    }
  }

  /*
   * First try to push to infinity. If that fails, try to push one level only.
   */
  int QuipSolver::tryPropagate(const Lemma & lem, Cube & reduced) {
    const Cube & c = lem.getCube();
    int level = lem.level;
    assert(level < INT_MAX);

    ConsecutionChecker * chk = cons_checker.get();
    if (options().excl_push) { chk = excl_checker.get(); }
    assert(chk);

    if (chk->consecution(c, INT_MAX, reduced)) {
      stats.cons_from_prop_cls++;
      return INT_MAX;
    } else if (chk->consecution(c, level, reduced)) {
      stats.cons_from_prop_cls++;
      return level + 1;
    }
    return level;
  }

  /*
   * Quip needs to override buildCex to handle reachable states
   */
  ReturnValue QuipSolver::buildCex(ProofObligation & obl) {
    ReturnValue rv = ReturnValue(MC::CEX);
    Cube init_cube = initCube();
    Cube cex_state = obl.cex_state;
    std::sort(init_cube.begin(), init_cube.end());
    std::sort(cex_state.begin(), cex_state.end());

    // TODO: fix ReachableStateManager so as to simplify this procedure and
    // also try to make sure it's correct
    std::vector<Transition> tmp;
    if (cex_state != init_cube) {
      ReachableState * r0 = rsman.intersect(obl.cube);
      assert(r0);
      // Skip the state from r0, because it will be repeated as po.cex_state
      ReachableState * prev_r = r0;
      r0 = r0->pre;

      while (r0) {
        tmp.push_back(Transition(r0->state, prev_r->inputs));
        r0 = r0->pre;
        prev_r = prev_r->pre;
      }

      // The reachable states will not go all the way back to the initial state,
      // they'll stop one step short. Add it here.
      tmp.push_back(Transition(init_cube, prev_r->inputs));
    }

    std::reverse(tmp.begin(), tmp.end());
    rv.cex = tmp;

    ProofObligation * po = &obl;
    while (po) {
      rv.cex.push_back(Transition(po->cex_state, po->inputs));
      po = po->parent;
    }
    return rv;
  }

  /*
   * (Re-) initializes the solvers.
   * Returns true if any of the solvers indicate the problem is trivial
   */
  bool QuipSolver::renewSAT() {
    return quipRenewSAT();
  }

  /*
   * In case QuipSolver ever needs to call renewSAT of a base class, we have
   * this. If QuipSolver::renewSAT called UMCEngine::renewSAT, it would be a
   * problem to call renewSAT from the constructor. We'd end up calling
   * UMCEngine::renewSAT twice (because the UMCEngine constructor would've
   * called it, then we'd call it again from the QuipSolver constructor).
   * This way, we have the quipPrepare/quipRenewSAT path that just
   * initializes Quip things, and the prepare/renewSAT path that can
   * be called externally to initialize everything.
   */
  bool QuipSolver::quipRenewSAT() {
    logger.verbose() << "renewSAT" << std::endl;

    bool trivial = cons_checker->renewSAT();
    trivial = trivial || (excl_checker && excl_checker->renewSAT());
    trivial = trivial || inf_checker->renewSAT();
    trivial = trivial || init_checker->renewSAT();
    trivial = trivial || lifter->renewSAT();

    return trivial;
  }

} // namespace UMC

