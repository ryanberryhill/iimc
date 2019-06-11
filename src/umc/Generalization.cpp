#include "UMCEngine.h"
#include "Generalization.h"

#include <algorithm>

namespace UMC {

  Generalizer::Generalizer(EngineGlobalState & gs,
                           ConsecutionChecker & cons,
                           bool random) :
        m_random(random),
        inductive_trace(gs.inductive_trace),
        model(gs.model),
        opts(gs.opts),
        ev(gs.ev),
        stats(gs.stats),
        cons_checker(cons),
        initiation_checker(gs.initiation_checker),
        logger(gs.logger)
  { }


  PrintCubePair Generalizer::pc(const Cube & cube) const {
    return std::make_pair(&cube, &ev);
  }

  /*
   * Essentially a wrapper around the consecution checker
   */
  bool Generalizer::consecution(Cube & c, int k, SAT::Assignment * asgn) const
  {
    return consecutionBudgeted(c, k, -1, asgn);
  }

  bool Generalizer::consecutionApprox(Cube & c, int k) const
  {
    return consecutionBudgeted(c, k, opts.gen_budget, NULL);
  }

  /*
   * Consecution with a decision budget. If the budget is exceeded the
   * instance is assumed to be SAT.
   */
  bool Generalizer::consecutionBudgeted(Cube & c, int k, int budget, SAT::Assignment * asgn) const
  {
    Cube reduced;
    ConsecutionOpts copts;
    copts.level = k;
    copts.cube = &c;
    copts.assignment = asgn;
    copts.reduced = &reduced;

    if (budget > 0) {
      copts.dec_budget = budget;
    }

    stats.consecution_calls++;
    stats.cons_from_gen++;
    bool cons = cons_checker.consecution(copts);

    // The consecution checker will set copts.timed_out to true in the event
    // of a timeout due to exceeding the decision budget
    if (budget > 0 && copts.timed_out) {
      stats.gen_timeouts++;
      assert(!cons);
    }

    if (cons) {
      c = reduced;
    }

    return cons;
  }

  /*
   * Syntactic check for initiation
   */
  bool Generalizer::initiation(const Cube & cube) const {
    return initiation_checker.initiation(cube);
  }

  /*
   * Add a literal from prev_cube to cube so that it satisfies initiation
   */
  void Generalizer::initiateCube(Cube & cube, const Cube & prev_cube) const {
    initiation_checker.initiateCube(cube, prev_cube);
  }

  /*
   * Binary search for highest level in [lo, hi] relative to which cube is
   * inductive. The cube is reduced through this process.
   */
  int Generalizer::binsearch(Cube & cube, int lo, int hi) const {
    // Try to push as far as possible with a binary search
#ifdef DEBUG
    assert(consecution(cube, lo));
#endif
    assert(hi < INT_MAX);
    int k = lo;
    int minlvl = lo, maxlvl = hi;
    while (minlvl <= maxlvl) {
      int checklvl = (minlvl + maxlvl) / 2;
      Cube copy = cube;
      if (consecutionApprox(copy, checklvl)) {
        assert(!copy.empty());
        cube = copy;
        k = checklvl;
        minlvl = checklvl + 1;
      } else {
        maxlvl = checklvl - 1;
      }
    }
    return k;
  }

  /*
   * Generalize the given cube by removing literals while maintaining inductiveness
   * lo - lowest level to consider
   * hi - highest level to consider
   */
  int Generalizer::generalize(int lo, int hi, Cube & cube) const
  {
    AutoTimer auto_timer(stats.gen_time);
    logger.logorrheic() << "generalizing cube " << pc(cube)
                        << " levels " << lo << " - " << hi
                        << std::endl;

    if (m_random)
    {
        std::random_shuffle(cube.begin(), cube.end());
    }

    // Check if absolutely invariant
    Cube c = cube;
    if (consecutionApprox(c, INT_MAX)) {
      mic(c, INT_MAX);
      cube = c;
      std::sort(cube.begin(), cube.end());
      return INT_MAX;
    }

    // Binary search for highlest level relative to which the cube
    // is inductive. Once the level is found, reduce the cube using
    // its core, and continue on to call down, mic, etc.
    int k = binsearch(cube, lo, hi);

    // use down to push forward as far as possible
    std::set<ID> dummy;
    for (; k < hi; ++k) {
      c = cube;
      if (down(c, k + 1, dummy)) {
        cube = c;
      } else {
        break;
      }
    }

    if (k == hi) {
      // Check if the generalized cube is absolutely invariant
      c = cube;
      if(down(c, INT_MAX, dummy)) {
        mic(c, INT_MAX);
        cube = c;
        std::sort(cube.begin(), cube.end());
        return INT_MAX;
      }
    }

    // definitely inductive relative to F_k
    mic(cube, k);
    std::sort(cube.begin(), cube.end());
    return k + 1;
  }

  /*
   * The join algorithm
   */
  bool Generalizer::join(Cube & cube, const SAT::Assignment & asgn, const std::set<ID> & keep) const
  {
    std::vector<ID> rcube;
    for (auto it = cube.begin(); it != cube.end(); it++) {
      SAT::Assignment::const_iterator ait = asgn.find(varOfLit(ev, *it));
      Expr::Op op = ev.op(*it);
      if ((op == Expr::Not && ait->second == SAT::True) ||
          (op == Expr::Var && ait->second == SAT::False)) {
        if (keep.find(*it) != keep.end()) {
          // about to drop a literal that should be kept
          return false;
        }
      }
      else {
        rcube.push_back(*it);
      }
    }
    cube = rcube;
    return true;
  }

  /*
   * Prepare a SAT::Assignment containing the variables for every literal
   * in cube, with the value unknown (to be filled in by the SAT solver).
   */
  SAT::Assignment Generalizer::prepareCubeAssignment(const Cube & cube) const {
    SAT::Assignment asgn;
    for (auto it = cube.begin(); it != cube.end(); it++) {
      asgn.insert(SAT::Assignment::value_type(varOfLit(ev, *it), SAT::Unknown));
    }
    return asgn;
  }

  Cube Generalizer::cubeFromAssignment(const SAT::Assignment & asgn) const {
    Cube cube;
    for (auto it = asgn.begin(); it != asgn.end(); it++) {
      assert(it->second != SAT::Unknown);
      ID assigned = it->first;
      ID nassigned = ev.apply(Expr::Not, assigned);
      ID x = it->second == SAT::False ? nassigned : assigned;
      cube.push_back(x);
    }
    std::sort(cube.begin(), cube.end());
    return cube;
  }

  /*
   * The up algorithm
   */
  void Generalizer::up(Cube & cube, int k, const std::set<ID> & keep) const {
#ifdef DEBUG
    assert(consecution(cube, k));
    assert(initiation(cube));
#endif
    prime_implicate(cube, k, keep);
  }

  /*
   * The prime_implicate algorithm. Find the smallest sub-cube of cube that
   * is inductive relative to F_k, keeping all of the literals from keep.
   */
  void Generalizer::prime_implicate(Cube & cube, int k, const std::set<ID> & keep) const {
    Cube sup(keep.begin(), keep.end());
    Cube s0;
    for (ID id : cube) {
      if (keep.find(id) == keep.end()) { s0.push_back(id); }
    }
    prime_implicate(k, sup, s0);

    cube = sup;
    cube.insert(cube.end(), s0.begin(), s0.end());
  }

  /*
   * Reduce the cube using the given core, shrinking cube to contain only the
   * literals common to cube and crits. If initiation (of sup U cube) is not
   * satisfied after reducing, a literal from prev_cube is added back in.
   */
  void Generalizer::reduce(Cube & cube, const Cube & sup, const Cube & prev_cube, const Cube & crits) const {
    Cube cube_copy = cube;
    Cube crits_copy = crits;
    std::sort(cube_copy.begin(), cube_copy.end());
    std::sort(crits_copy.begin(), crits_copy.end());

    auto it = std::set_intersection(cube_copy.begin(), cube_copy.end(),
                                    crits_copy.begin(), crits_copy.end(),
                                    cube.begin());
    cube.resize(it - cube.begin());

    if (!sup.empty() && !initiation(sup) && !initiation(cube)) {
      // Put back a literal
      initiateCube(cube, prev_cube);
    }
#ifdef DEBUG
    Cube c = cube_copy;
    c.insert(c.end(), sup.begin(), sup.end());
    assert(initiation(c));
    c = cube;
    c.insert(c.end(), sup.begin(), sup.end());
    assert(initiation(c));
#endif
  }

  /*
   * Recursive version of prime_implicate, following the description of the
   * optimal version of prime_implicate from the oroginal paper by Bradley and
   * Manna.
   */
  void Generalizer::prime_implicate(int k, const Cube & sup, Cube & s0) const {
#ifdef DEBUG
    Cube c = sup;
    c.insert(c.end(), s0.begin(), s0.end());
    std::sort(c.begin(), c.end());
    std::set<ID> cube_set(c.begin(), c.end());
    // no duplication
    assert(cube_set.size() == c.size());
    // The full cube satisfies the predicate (i.e., initiation and
    // k-consecution)
    logger.verbose() << "PI " << pc(c) << std::endl;
    assert(initiation(c));
    assert(consecution(c, k));
#endif
    // If s0 is size 1, the single element of s0 is necessary for
    // sup U s0 to be inductive.
    // If 0 is empty, then sup must satisfy both on its own
    if (s0.size() <= 1) {
      Cube sup_copy = sup;
      if (!sup.empty() && initiation(sup) && consecution(sup_copy, k)) {
        s0.clear();
      }
      return;
    }

    // Otherwise, split s0 into l0 and r0
    size_t mid = s0.size() / 2;
    auto mid_it = s0.begin() + mid;
    Cube l0(s0.begin(), mid_it);
    Cube r0(mid_it, s0.end());

    Cube sup_l0 = sup;
    sup_l0.insert(sup_l0.end(), l0.begin(), l0.end());

    if (initiation(sup_l0) && consecution(sup_l0, k)) {
      // l0 contains the necessary elements, recurse after reducing
      Cube orig = l0;
      reduce(l0, sup, orig, sup_l0);
      prime_implicate(k, sup, l0);
      s0 = l0;
      return;
    }

    Cube sup_r0 = sup;
    sup_r0.insert(sup_r0.end(), r0.begin(), r0.end());

    if (initiation(sup_r0) && consecution(sup_r0, k)) {
      // r0 contains the necessary elements, recurse after reducing
      Cube orig = r0;
      reduce(r0, sup, orig, sup_r0);
      prime_implicate(k, sup, r0);
      s0 = r0;
      return;
    }

    // Necessary elements are in both r0 and l0
    // Construct l by using sup U r0 as the support set
    // Construct r by using sup U l as the support set (note not l0)
    // Return (in s0) r U l
    Cube l = l0;
    prime_implicate(k, sup_r0, l);
    assert(!l.empty());
    Cube sup_l = sup;
    sup_l.insert(sup_l.end(), l.begin(), l.end());
    prime_implicate(k, sup_l, r0);
    s0 = l;
    s0.insert(s0.end(), r0.begin(), r0.end());
  }

  /*
   * The down algorithm with support for CTGs
   */
  bool Generalizer::down(Cube & cube, int k, const std::set<ID> & keep, int limit) const {
    SAT::Assignment asgn = prepareCubeAssignment(cube);

    if (limit < 0) {
      limit = opts.ctg_depth;
    }

    int ctgs = 0;
    int max_ctgs = opts.num_ctgs;

    while (true) {
      if (!initiation(cube)) {
        return false;
      } else if (consecution(cube, k, &asgn)) {
        return true;
      } else { // !consecution, asgn is a (F_k & cube)-state and CTG
        // First check if CTGs are allowed. If so, then
        // check if initiation and for induction relative to F_{i-1}
        bool do_ctg = limit > 0 && ctgs < max_ctgs && k > 0 && k < INT_MAX;
        // Convert asgn to a cube s if necessary
        Cube s = do_ctg ? cubeFromAssignment(asgn) : Cube();

        if (do_ctg && initiation(s) && consecutionApprox(s, k - 1)) {
          assert(opts.num_ctgs > 0 && opts.ctg_depth > 0);
          assert(!s.empty());
          // If so, push as far as possible using binsearch and then run MIC
          ctgs++;
          int max_level = inductive_trace.getMaxFrame();
          int level = binsearch(s, k - 1, max_level);
          assert(level >= k - 1);
          assert(level < INT_MAX);
          if (level >= max_level && consecutionApprox(s, INT_MAX)) {
            level = INT_MAX;
          }

          mic(s, level, limit - 1);

          // Add the cube
          inductive_trace.addCube(s, level < INT_MAX ? level + 1 : level);
        } else {
          // Either we're at level 0 and can't do anything, or we've tried too
          // many times, or the CTG wasn't inductive, or CTGs are disabled.
          // Reset the CTG counter and join.
          ctgs = 0;
          if (!join(cube, asgn, keep)) {
            return false;
          }
        }
      }
    }
  }

  /*
   * Compute an approximately minimally inductive cube (relative to F_k),
   * considering CTGs (in down) if enabled
   */
  void Generalizer::mic(Cube & cube, int k, int limit) const {
    std::set<ID> keep;
    while (true) {
      // Run up if applicable
      if (k == 0 || (int) cube.size() > opts.up_threshold) {
        up(cube, k, keep);
      }

      // Try brute force reduction a configurable number of times
      unsigned int i = 0;
      int cnt = opts.gen_fails;
      for (; i < cube.size() && cnt > 0; ++i) {
        if (keep.find(cube[i]) != keep.end()) {
          continue;
        }

        std::vector<ID> dcube(cube.size() - 1);
        for (unsigned int j = 0, l = 0; j < cube.size(); ++j) {
          if (j != i) {
            dcube[l++] = cube[j];
          }
        }

        if (down(dcube, k, keep, limit)) {
          cube = dcube;
          break;
        } else {
          keep.insert(cube[i]);
          --cnt;
        }
      }

      if (i == cube.size() || cnt < 0) return;
    }
  }

  /*
   * Generalize the given cube by removing literals while maintaining inductiveness
   * lo - lowest level to consider
   * hi - highest level to consider
   */
  int IterativeGeneralizer::generalize(int lo, int hi, Cube & cube) const {
    AutoTimer auto_timer(stats.gen_time);
    logger.logorrheic() << "generalizing cube " << pc(cube)
                        << " levels " << lo << " - " << hi
                        << std::endl;

#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
    assert(initiation(cube));
    assert(consecution(cube, lo));
#endif
    assert(hi < INT_MAX);

    int k = lo;
    // Check if inductive at infinity
    if (consecutionApprox(cube, INT_MAX)) {
      k = INT_MAX;
    }

    // Generalize as much as possible at k
    bool changed = true;
    for (int i = 0; changed && i < opts.gen_fails; ++i) {
      changed = false;
      // Drop literals in a round robin fashion
      for (size_t i = 0; i < cube.size(); ++i) {
        Cube copy = cube;
        ID lit = cube[i];
        copy.erase(copy.begin() + i);
        if (initiation(copy) && consecutionApprox(copy, k)) {
          // lit was dropped successfully
          assert(copy.size() < cube.size());
          cube = copy;
          changed = true;
#ifdef DEBUG
          assert(std::is_sorted(cube.begin(), cube.end()));
#endif
          // Find the next literal after lit (cube is sorted)
          for (i = 0; i < cube.size(); ++i) {
            if (cube[i] > lit) { break; }
          }
        }
      }
    }

#ifdef DEBUG
    assert(std::is_sorted(cube.begin(), cube.end()));
    assert(initiation(cube));
    assert(consecution(cube, k));
#endif

    if (k == INT_MAX) { return INT_MAX; }

    // Try to push as far as possible with a binary search
    k = binsearch(cube, lo, hi);

    if (k == hi && consecutionApprox(cube, INT_MAX)) {
      return INT_MAX;
    }

    return k + 1;
  }

}

