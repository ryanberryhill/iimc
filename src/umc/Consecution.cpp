#include "Consecution.h"
#include "ExprAttachment.h"
#include "CNFAttachment.h"
#include "Random.h"
#include "UMCEngine.h"

namespace UMC {

  LemmaFilter no_bad_no_ugly = [](const Lemma & lem) { return !lem.bad && !lem.ugly; };

  ConsecutionChecker::ConsecutionChecker(
                         const EngineGlobalState & gs,
                         std::set<ID> init_state,
                         ID property,
                         ID bad)
    : badvar(bad),
      property(property),
      stale(false),
      umc_opts(gs.opts),
      inductive_trace(gs.inductive_trace),
      ev(gs.ev),
      model(gs.model),
      stats(gs.stats),
      logger(gs.logger),
      initially(init_state),
      initiation_checker(gs.initiation_checker)
  {
    inductive_trace.registerConsecutionChecker(*this);
    constructTR();
  }


  bool ConsecutionChecker::loadTR(SAT::Manager & manager) {
    bool trivial = false;

    try {
      manager.add(tr_clauses);
    }
    catch (SAT::Trivial const & tr) {
      assert(!tr.value());
      trivial = true;
    }

    return trivial;
  }

  void ConsecutionChecker::cleanupTR() {
    tr_clauses.clear();
  }

  /*
   * Loads all lemmas in the inductive trace into the SAT manager(s).
   */
  void ConsecutionChecker::loadAllFrames() {
    for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
      doLoadLemma(lem);
    }
  }

  void ConsecutionChecker::loadLemma(const Lemma & lem) {
    if (!isFilteredOut(lem)) {
      doLoadLemma(lem);
    }
  }

  /*
   * Returns an activation literal with the associated integer index.  For the
   * standard consecution checker, the index would refer to the level of a
   * lemma in the inductive trace. However, for e.g., support set computations,
   * each Lemma would have its own unique activation literal, possibly using
   * the cube ID as the index.
   */
  ID ConsecutionChecker::activationLit(int index) const {
    auto it = index_to_act.find(index);
    if (it != index_to_act.end()) {
      ID act = it->second;
#ifdef DEBUG
      {
        auto found = act_to_index.find(act);
        assert(found != act_to_index.end());
        assert(found->second == index);
      }
#endif
      return act;
    } else {
      std::stringstream buf;
      buf << "act_" << index;
      ID act = ev.newVar(buf.str());
      index_to_act[index] = act;
      act_to_index[act] = index;
      return act;
    }
  }

  /*
   * Returns the index associated with the given activation literal (can
   * be given with positive or negative polarity). The ID must be a known
   * activation literal, as returned by activationLit.
   */
  int ConsecutionChecker::inverseActivationLit(ID lit) const {
    ID var = toVar(lit);

    auto it = act_to_index.find(var);
    assert(it != act_to_index.end());
    int index = it->second;
#ifdef DEBUG
    {
      auto found = index_to_act.find(index);
      assert(found != index_to_act.end());
      assert(found->second == var);
    }
#endif

    return index;
  }

  /*
   * Returns true if and only if the given literal is an activation variable.
   */
   bool ConsecutionChecker::isActivationLit(ID lit) const {
    ID var = toVar(lit);

    auto it = act_to_index.find(var);
    if (it != act_to_index.end()) {
#ifdef DEBUG
      {
        int index = it->second;
        auto found = index_to_act.find(index);
        assert(found != index_to_act.end());
        assert(found->second == var);
      }
#endif
      return true;
    }

    return false;
  }

  /*
   * Returns the variable corresponding to the given literal. In other words,
   * removes any negation if present.
   */
  ID ConsecutionChecker::toVar(ID lit) const {
    return varOfLit(ev, lit);
  }

  /*
   * Construct and return a vector of clauses representing the constraints.
   */
  std::vector<Clause> ConsecutionChecker::getConstraintClauses() {
    const ExprAttachment * eat = (const ExprAttachment *) model.constAttachment(Key::EXPR);
    const auto & constraints = eat->constraintFns();
    std::vector<Clause> constraint_clauses;

    if (!constraints.empty()) {
      // Construct a map from latches to their Boolean values in the initial
      // state. This is used to see if constraints reduce to primitive true or
      // false
      Expr::IDMap initial;
      for (auto it = initially.begin(); it != initially.end(); ++it) {
        ID latch = toVar(*it);
        ID latch_value = (latch == *it ? ev.btrue() : ev.bfalse());
        initial.insert(std::make_pair(latch, latch_value));
      }

      for (auto it = constraints.begin(); it != constraints.end(); ++it) {
        ID fn = *it;
        ID sub = varSub(ev, initial, fn);
        if (sub == ev.btrue()) { continue; }
        // if the constraint is equal to bfalse the problem is trivially safe.
        // We won't find it here, but the solver will quickly figure it out.
        Expr::tseitin(ev, fn, constraint_clauses);
        // IC3 also does a semantic check using SAT to see if the constraint
        // isn't implied by the initial state, but we don't have that here
      }
    }

    model.constRelease(eat);
    return constraint_clauses;
  }

  /*
   * Construct the transition relation. This is done as follows. The plain CNF
   * (i.e., it just specifies the relations between state variables,
   * next-states, inputs, and outputs (?)) is augmented with two additional
   * expressons. These expressions are (bad = property) and (bad' = property').
   */
  void ConsecutionChecker::constructTR() {
    cleanupTR();
    auto cnfat = model.attachment<CNFAttachment>(Key::CNF);
    const ExprAttachment * eat = (const ExprAttachment *) model.constAttachment(Key::EXPR);

    // clauses: the clauses that make up the transition relation
    // p_clauses: enforcing bad = property
    // pprime_clauses: enforcing bad' = property'
    // constraint_clauses: restrict state, primed state
    std::vector<Clause> clauses, pprime_clauses, p_clauses, constraint_clauses;
    ID p = getProperty();
    ID pprime = getPropertyPrime();
    ID bad = getBad();
    ID badprime = getBadPrime();

    // bad = P
    ID p_eq_bad = ev.apply(Expr::Equiv, bad, p);
    // bad' = P'
    ID p_eq_bad_prime = ev.apply(Expr::Equiv, badprime, pprime);

    // Plain CNF is just the transition relation
    clauses = cnfat->getPlainCNF();
    Expr::tseitin(ev, p_eq_bad_prime, pprime_clauses);
    Expr::tseitin(ev, p_eq_bad, p_clauses);

    // TODO: The Slice action can introduce constraints. I think we handle them
    // correctly but something else goes wrong in Quip.
    //constraint_clauses = getConstraintClauses();
    assert(eat->constraints().empty());

    assert(!clauses.empty());
    assert(!p_clauses.empty());
    assert(!pprime_clauses.empty());

    tr_clauses.insert(tr_clauses.end(), clauses.begin(), clauses.end());
    tr_clauses.insert(tr_clauses.end(), p_clauses.begin(), p_clauses.end());
    tr_clauses.insert(tr_clauses.end(), pprime_clauses.begin(), pprime_clauses.end());

    model.constRelease(eat);
    model.release(cnfat);
  }

  /*
   * This function or an overload of it must be called any time a lemma is
   * deleted. The consecution checker will do whatever is appropriate.
   * This almost certainly means marking itself stale, because there is no
   * way to remove the lemma from the solvers.
   */
  void ConsecutionChecker::lemmaDeleted(CubeID id) {
    const Lemma & lem = inductive_trace.getActiveLemma(id);
    lemmaDeleted(lem);
  }

  void ConsecutionChecker::lemmaDeleted(const Lemma & lem) {
    (void) lem;
    markStale();
  }

  /*
   * This function or an overload of it must be called any time a lemma is
   * newly-added to the trace. The consecution checker will do whatever is
   * appropriate. In the case of the standard one, that is just the call
   * loadLemma. However, other checkers may need to do something different.
   */
  void ConsecutionChecker::lemmaAdded(CubeID id) {
    const Lemma & lem = inductive_trace.getActiveLemma(id);
    lemmaAdded(lem);
  }

  void ConsecutionChecker::lemmaAdded(const Lemma & lem) {
    loadLemma(lem);
  }

  /*
   * This function or an overload of it must be called any time a lemma's
   * metadata (e.g., ugliness, badness, but *not its level*) is modified.  The
   * consecution checker will take the appropriate steps. We just call
   * loadLemma typically, since the loadFilter may have filtered out the lemma
   * before, but after the change no longer filter it out.
   */
  void ConsecutionChecker::lemmaModified(CubeID id) {
    const Lemma & lem = inductive_trace.getActiveLemma(id);
    lemmaModified(lem);
  }

  void ConsecutionChecker::lemmaModified(const Lemma & lem) {
    loadLemma(lem);
  }

  /*
   * This function or an overload must be called any time a lemma's level is
   * increased. Demoting a lemma must be handled differently.  The consecution
   * checker will take the appropriate steps. In the case of the standard
   * checker, it will be added to the SAT manager with the new level. However,
   * for e.g., support computations, nothing should be done when a lemma is
   * promoted to a level other than infinity.
   */
  void ConsecutionChecker::lemmaPromoted(CubeID id) {
    const Lemma & lem = inductive_trace.getActiveLemma(id);
    lemmaPromoted(lem);
  }

  void ConsecutionChecker::lemmaPromoted(const Lemma & lem) {
    loadLemma(lem);
  }

  /*
   * This function or an overload must be called any time a lemma's level is
   * decreased. The consecution checker will take the appropriate steps. This
   * probably means just marking itself stale.
   */
  void ConsecutionChecker::lemmaDemoted(CubeID id) {
    const Lemma & lem = inductive_trace.getActiveLemma(id);
    lemmaDemoted(lem);
  }

  void ConsecutionChecker::lemmaDemoted(const Lemma & lem) {
    (void) lem;
    markStale();
  }

  /*
   * Syntactic check for initiation
   */
  bool ConsecutionChecker::initiation(const Cube & cube) const {
    return initiation_checker.initiation(cube);
  }


  /*
   * Reduce cube c (and store the result in reduced) by taking the intersection
   * of c and crits (which should represent the critical assumptions
   */
  void ConsecutionChecker::reduceCube(const Cube & c,
                                      Cube & reduced,
                                      const Cube & crits) const
  {
    reduced.clear();

    Cube crits_sorted = crits;
    std::sort(crits_sorted.begin(), crits_sorted.end());

    for (auto it = c.begin(); it != c.end(); it++) {
      if (binary_search(crits_sorted.begin(), crits_sorted.end(),
                        Expr::primeFormula(ev, *it))) {
        reduced.push_back(*it);
      }
    }

    if (!initiation(reduced)) {
      // Put back a literal in order to make reduced satisfy initiation
      for (auto it = c.rbegin(); it != c.rend(); it++) {
        ID lit = *it;
        ID nlit = ev.apply(Expr::Not, lit);
        if (initially.count(nlit)) {
          reduced.push_back(lit);
          std::sort(reduced.begin(), reduced.end());
          assert(initiation(reduced));
          break;
        }
      }
    }
  }

  /*
   * Construct and return assumptions for the cube, unprimed cube, extra
   * assumptions, and any member of ConsecutionOpts that are applicable to
   * all types of ConsecutionChecker
   */
  Expr::IDVector ConsecutionChecker::defaultAssumptions(ConsecutionOpts & opts) const {
    // Should handle the assumptions for opts.cube
    Expr::IDVector assumps = defaultCriticalAssumptions(opts);

    if (opts.unprimed_cube) {
      assumps.insert(assumps.end(),
                     opts.unprimed_cube->begin(),
                     opts.unprimed_cube->end());
    }

    if (opts.extra_assumps) {
      assumps.insert(assumps.end(),
                     opts.extra_assumps->begin(),
                     opts.extra_assumps->end());
    }

    return assumps;
  }

  /*
   * Construct and return the default critical assumptions. This usually
   * refers to the cube alone.
   */
  Expr::IDVector ConsecutionChecker::defaultCriticalAssumptions(ConsecutionOpts & opts) const {
    Expr::IDVector assumps;
    if (opts.cube) {
      const Cube & cube = *opts.cube;

      for (ID id : cube) {
        assumps.push_back(ev.prime(id));
      }
    }

    return assumps;
  }

  bool ConsecutionChecker::consecution(ConsecutionOpts & opts) {
    // Check if another thread has already found the answer. This is handled
    // through Random so that other tactics check every time they request a
    // random number. However, our engines don't ever do that, so we
    // explicitly call check_future() here.
    Random::check_future();
    // For now, we're assuming each consecution checker does a single SAT call
    // and spends ~100% of its time doing SAT
    stats.sat_calls++;
    AutoTimer auto_timer(stats.sat_time);

    if (stale) {
      std::string name = boost::core::demangle(typeid(*this).name());
      throw std::logic_error("Consecution called on a stale instance of " + name);
    }

    return doConsecution(opts);
  }

  bool ConsecutionChecker::consecution(const Cube & c, int k) {
    ConsecutionOpts copts;
    copts.cube = &c;
    copts.level = k;
    return doConsecution(copts);
  }

  bool ConsecutionChecker::consecution(const Cube & c, int k, Cube & reduced) {
    ConsecutionOpts copts;
    copts.cube = &c;
    copts.level = k;
    copts.reduced = &reduced;
    return doConsecution(copts);
  }

  bool ConsecutionChecker::renewSAT() {
    stale = false;
    return doRenewSAT();
  }

  bool LevelBasedConsecutionChecker::doRenewSAT() {
    // The view must be destroyed before the manager
    sat_view.reset();
    sat_man.reset(model.newSATManager());
    bool trivial = loadTR(*sat_man);
    if (trivial) { return true; }

    sat_view.reset(sat_man->newView(ev, backend()));
    if (umc_opts.use_abbr) {
      sat_view->lockInModel();
    }

    loadAllFrames();

    return false;
  }

  /*
   * Loads the given lemma into the SAT manager(s) with a suitable activation
   * literal (if needed). In this consecution checker, there is only
   * one SAT manager and activation literals are level-based. However, one
   * could imagine a consecution checker where each level has its own
   * SAT manager and no activation literals.
   */
  void LevelBasedConsecutionChecker::doLoadLemma(const Lemma & lem) {
    if (!SATInitialized()) {
      // SAT hasn't been initialized, do nothing
      return;
    }
    const Cube & cube = lem.getCube();
    int level = lem.level;

    // Convert the cube to a clause
    Clause cls;
    Expr::complement(ev, cube, cls);

    // Add the clause at every level up to and including level
    if (level < INT_MAX) {
      for (int i = 0; i <= level; ++i) {
        ID act_lit = ev.apply(Expr::Not, activationLit(i));
        Clause c_act(cls);
        c_act.push_back(act_lit);
        sat_man->add(c_act);
      }
    } else {
      assert(level == INT_MAX);
      sat_man->add(cls);
    }
  }

  bool LevelBasedConsecutionChecker::doConsecution(ConsecutionOpts & opts) {
    assert(opts.support_set == NULL);
    assert(opts.level >= 0);
    assert(opts.cube || opts.unprimed_cube || opts.extra_assumps);
    assert(!(opts.cube == NULL && opts.reduced != NULL));
    assert(!opts.filter);

    int level = opts.level;
    int dec_budget = opts.dec_budget;
    int * conf = nullptr;

    Expr::IDVector assumps, cassumps;
    assumps = defaultAssumptions(opts);
    cassumps = defaultCriticalAssumptions(opts);

    SAT::GID gid = SAT::NULL_GID;
    if (opts.cube) {
      const Cube & cube = *opts.cube;

      Clause cc;
      Expr::complement(ev, cube, cc);
      gid = sat_view->newGID();
      sat_view->add(cc, gid);
    }

    if (level < INT_MAX) {
      assumps.push_back(activationLit(level));
    }

    if (dec_budget > 0) {
      conf = &dec_budget;
    }

    bool is_sat = sat_view->sat(&assumps,
                                opts.assignment,
                                opts.reduced ? &cassumps : NULL,
                                SAT::NULL_GID,
                                false,
                                NULL,
                                NULL,
                                conf);

    if (dec_budget > opts.dec_budget) {
      opts.timed_out = true;
      assert(is_sat);
    } else {
      opts.timed_out = false;
    }

    if (!is_sat && opts.reduced) {
      assert(opts.cube);
      reduceCube(*opts.cube, *opts.reduced, cassumps);
    }

    if (opts.cube) {
      assert(gid != SAT::NULL_GID);
      sat_view->remove(gid);
    }

    return !is_sat;
  }

  /*
   * The InitialChecker loads every lemma with no activation. For a lemma
   * to be valid it must include all initial states, so this is fine.
   * It could be argued that it's slower than only loading the legitmate
   * F_0 lemmas, but the extra clauses might make it easier to prove UNSAT.
   * Either way, checking if a state is initial using SAT should be rare
   * so it shouldn't matter much.
   */
  void InitialChecker::doLoadLemma(const Lemma & lem) {
    Clause cls;
    Expr::complement(ev, lem.getCube(), cls);
    sat_man->add(cls);
  }

  /*
   * The InfChecker loads only infinity lemmas.
   */
  void InfChecker::doLoadLemma(const Lemma & lem) {
    if (lem.level == INT_MAX) {
      Clause cls;
      Expr::complement(ev, lem.getCube(), cls);
      sat_man->add(cls);
    }
  }

  /*
   * The InfOnlyConsecutionChecker loads only infinity lemmas and
   * uses no activation literals.
   */
  void InfOnlyConsecutionChecker::doLoadLemma(const Lemma & lem) {
    if (lem.level == INT_MAX) {
      Clause cls;
      Expr::complement(ev, lem.getCube(), cls);
      sat_man->add(cls);
    }
  }

  /*
   * The UNSATCoreLifter does not support consecution
   */
  bool UNSATCoreLifter::doConsecution(ConsecutionOpts & opts) {
    (void) opts;
    throw std::logic_error("`doConsecution' called on an UNSATCoreLifter, "
                           "call `lift' instead");
  }

  /*
   * Interface to the lifter. Perform whatever kind of lifting is needed
   */
  void UNSATCoreLifter::lift(Cube & t,
                             const Cube & inputs,
                             const Cube & p_inputs,
                             const Cube & s) const {
    // TODO: handle lifting type better
    AutoTimer auto_timer(stats.lift_time);
    if (options().lift_style == "min") {
      minLift(t, inputs, p_inputs, s);
    } else if (options().lift_style == "iter") {
      iterLift(t, inputs, p_inputs, s);
    } else if (options().lift_style == "single") {
      bool cons = oneLift(t, inputs, p_inputs, s);
      assert(cons);
    } else {
      assert(false);
    }
#ifdef DEBUG
    assert(std::is_sorted(t.begin(), t.end()));
#endif
  }

  /*
   * Perform lifting. executes the query:
   * (t AND inputs AND T AND p_inputs AND ~s')
   * and lifts t using the UNSAT core such that all lifted-states
   * can reach ~s in one step.
   */
  bool UNSATCoreLifter::oneLift(Cube & t,
                                const Cube & inputs,
                                const Cube & p_inputs,
                                const Cube & s,
                                bool exact) const {
    AutoTimer auto_timer(stats.sat_time);
    stats.sat_calls++;

    Expr::IDVector assumps, cassumps;
    assumps.insert(assumps.end(), t.begin(), t.end());
    cassumps = assumps;
    assumps.insert(assumps.end(), inputs.begin(), inputs.end());
    assumps.insert(assumps.end(), p_inputs.begin(), p_inputs.end());

    // Prime and negate s
    Clause neg_s_prime = s;
    for (ID & lit : neg_s_prime) {
      lit = ev.apply(Expr::Not, ev.prime(lit));
    }

    SAT::GID gid = sat_view->newGID();
    sat_view->add(neg_s_prime, gid);
    bool sat = false;
    if (exact) {
      sat = sat_view->sat(&assumps, NULL, &cassumps);
    } else {
      int dec_budget = umc_opts.lift_budget;
      sat = sat_view->sat(&assumps, NULL, &cassumps,
                          SAT::NULL_GID, false, NULL, NULL,
                          dec_budget > 0 ? &dec_budget : NULL);
      if (dec_budget > umc_opts.lift_budget && sat) {
        stats.lift_timeouts++;
      }
    }
    sat_view->remove(gid);

    // It's possible to have no critical assumptions - this means all
    // states can reach a ~s-state. Just leave t as-is in that case.
    if (!sat && !cassumps.empty()) {
      t = cassumps;
    }

    return !sat;
  }

  /*
   * Performs lifting in an iterative fashion. Calls lift repeatedly until
   * the cube converges
   */
  void UNSATCoreLifter::iterLift(Cube & t,
                                 const Cube & inputs,
                                 const Cube & p_inputs,
                                 const Cube & s) const {
    Cube old_t;
    while (old_t != t) {
      old_t = t;
      bool cons = oneLift(t, inputs, p_inputs, s);
      assert(cons);
    }
  }

  /*
   * Computes a minimal lifting of the given cube.
   */
  void UNSATCoreLifter::minLift(Cube & t,
                                const Cube & inputs,
                                const Cube & p_inputs,
                                const Cube & s) const {
#ifdef DEBUG
    assert(std::is_sorted(t.begin(), t.end()));
#endif

    // First do a normal lifting to clear the low-hanging fruit
    oneLift(t, inputs, p_inputs, s);

    for (size_t i = 0; i < t.size(); ++i) {
      ID lit = t[i];
      Cube test_cube = t;
      test_cube.erase(test_cube.begin() + i);

      if (oneLiftApprox(test_cube, inputs, p_inputs, s)) {
        assert(test_cube.size() < t.size());
        t = test_cube;
#ifdef DEBUG
        assert(std::is_sorted(t.begin(), t.end()));
#endif
        // Find the index of the literal we dropped. Of course, it won't be
        // there because we dropped it, so exploit the fact that t is sorted
        // in ascending order
        for (i = 0; i < t.size(); ++i) {
          if (t[i] > lit) { break; }
        }
      }
    }
  }

  /*
   * The activation-based checker can tolerate deletion except in the case
   * of F_infinity, and even then it's fine if the deleted lemma is subsumed
   * by another infinity lemma
   */
  void ActivationBasedConsecutionChecker::lemmaDeleted(const Lemma & lem) {
#ifdef DEBUG
    if (lem.level == INT_MAX && !isFilteredOut(lem)) {
      // the lemma must be subsumed by another infinity lemma for this to be a
      // safe operation
      const Frame & finf = inductive_trace.getInfFrame();
      bool found = false;
      for (CubeID id : finf) {
        const Cube & cube = inductive_trace.getCube(id);
        if (subsumes(lem.getCube(), cube) &&
            inf_loaded_lemmas.find(id) != inf_loaded_lemmas.end()) {
          found = true;
          break;
        }
      }
      assert(found);
    }
#else
    (void) lem;
#endif
  }

  /*
   * Load the lemma with its own activation literal if necessary.
   */
  void ActivationBasedConsecutionChecker::doLoadLemma(const Lemma & lem) {
    if (!SATInitialized()) {
      // SAT hasn't been initialized, do nothing
      return;
    }

    CubeID id = lem.getID();
    const Cube & cube = lem.getCube();
    int level = lem.level;

    // Convert the cube to a clause
    Clause cls;
    Expr::complement(ev, cube, cls);

    if (level < INT_MAX) {
      if (loaded_lemmas.find(id) != loaded_lemmas.end()) {
        // We've already loaded this lemma, no need to reload it
        return;
      }

      // Add the activation literal
      ID act = activationLit(id);
      cls.push_back(act);

      // Add to the solver
      sat_man->add(cls);

      // Add to loaded set
      loaded_lemmas.insert(id);
    } else {
      assert(level == INT_MAX);
      if (inf_loaded_lemmas.find(id) != inf_loaded_lemmas.end()) {
        // We've already loaded this lemma with no activation
        return;
      }

      // Add to the solver
      sat_man->add(cls);

      // Add to the infinity loaded set
      inf_loaded_lemmas.insert(id);
    }
  }

  /*
   * The activation-based checker also maintains sets representing the lemmas
   * that have already been loaded at finite levels and at infinity,
   * respectively.  They neeed to be cleared during renewSAT
   */
  bool ActivationBasedConsecutionChecker::doRenewSAT() {
    loaded_lemmas.clear();
    inf_loaded_lemmas.clear();
    bool result = LevelBasedConsecutionChecker::doRenewSAT();
    return result;
  }

  /*
   * The activation-based checker must force all activation literals to zero
   * for frames that participate in the query. It can also be made to consider
   * ugly, bad, etc.
   */
  bool ActivationBasedConsecutionChecker::doConsecution(ConsecutionOpts & opts) {
    assert(opts.level >= 0);
    // No cube, no unprimed cube, and no extra assumptions makes no sense
    assert(opts.cube || opts.unprimed_cube || opts.extra_assumps);
    // No cube given but requesting a reduced cube makes no sense
    assert(!(opts.cube == NULL && opts.reduced != NULL));
    // No cube given but requesting a support set makes no sense
    assert(!(opts.cube == NULL && opts.support_set != NULL));
    // Not implemented
    if (opts.dec_budget > 0) {
      throw std::logic_error("ActivationBasedConsecutionChecker support for budgets is not implemented");
    }

    bool do_support = opts.support_set != NULL;

    Expr::IDVector assumps, cassumps;
    assumps = defaultAssumptions(opts);
    cassumps = defaultCriticalAssumptions(opts);

    int level = opts.level;

    for (int i = inductive_trace.getMaxFrame(); i >= level; --i) {
      const Frame & fi = inductive_trace.getFrame(i);
      for (CubeID id : fi) {
        // Exclude deleted lemmas if they're loaded
        if (inductive_trace.isDeleted(id)) {
          assert(inf_loaded_lemmas.find(id) == inf_loaded_lemmas.end());
          continue;
        }

        const Lemma & lem = inductive_trace.getActiveLemma(id);

        // Filter out lemmas if the filter is present
        if (isFilteredOut(lem)) {
          continue;
        }

        // Also check for the option filter
        if (opts.filter && !opts.filter(lem)) {
          continue;
        }

        assert(loaded_lemmas.find(id) != loaded_lemmas.end());

        ID act = activationLit(id);
        ID nact = ev.apply(Expr::Not, act);
        assumps.push_back(nact);

        if (do_support) {
          cassumps.push_back(nact);
        }
      }
    }

    SAT::GID gid = SAT::NULL_GID;
    if (opts.cube) {
      const Cube & cube = *opts.cube;

      Clause cc;
      Expr::complement(ev, cube, cc);
      gid = sat_view->newGID();
      assert(gid != SAT::NULL_GID);
      sat_view->add(cc, gid);
    }

    bool is_sat = sat_view->sat(&assumps,
                                opts.assignment,
                                opts.reduced || do_support ? &cassumps : NULL,
                                SAT::NULL_GID,
                                false,
                                NULL,
                                NULL);

    if (!is_sat && opts.reduced) {
      assert(opts.cube);
      assert(gid != SAT::NULL_GID);
      reduceCube(*opts.cube, *opts.reduced, cassumps);
    }

    if (opts.cube) {
      assert(gid != SAT::NULL_GID);
      sat_view->remove(gid);
    }

    if (!is_sat && do_support) {
      *opts.support_set = computeSupport(cassumps);
    }

    return !is_sat;
  }

  std::set<CubeID> ActivationBasedConsecutionChecker::computeSupport(const Cube & crits) const {
    std::set<CubeID> support;
    for(auto it = crits.begin(); it != crits.end(); ++it) {
      ID crit = *it;

      if (isActivationLit(crit)) {
        CubeID support_id = (CubeID) inverseActivationLit(crit);
        support.insert(support_id);
      }
    }

    return support;
  }

  bool MultiSATConsecutionChecker::isLoaded(int level, CubeID id) const {
    auto it = levels.find(level);
    if (it == levels.end()) {
      return false;
    }

    const SATLevel & sat_level = it->second;
    auto const & loaded = sat_level.loaded_lemmas;
    return (loaded.find(id) != loaded.end());
  }

  void MultiSATConsecutionChecker::setLoaded(int level, CubeID id) {
    auto it = levels.find(level);
    assert(it != levels.end());
    SATLevel & sat_level = it->second;
    auto & loaded = sat_level.loaded_lemmas;
    loaded.insert(id);
  }

  void MultiSATConsecutionChecker::initSAT(int level) {
    auto it = levels.find(level);

    assert(it == levels.end());

    SAT::Manager * manager = model.newSATManager();
    bool trivial = loadTR(*manager);
    assert(!trivial);
    SAT::Manager::View * view = manager->newView(ev, backend());
    levels.emplace(level, SATLevel(manager, view));

    for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
      if (safeToAdd(lem, level)) {
        addLemmaToManager(lem, *manager);
        // No need to check ifLoaded, this level is brand new
        setLoaded(level, lem.getID());
      }
    }
  }

  /*
   * Return true if the lemma belongs in the manager for the given level.
   * Can be overridden to implement e.g., exclusion of bad and ugly lemmas.
   */
  bool MultiSATConsecutionChecker::safeToAdd(const Lemma & lem, int level) const {
    if (isFilteredOut(lem)) { return false; }
    return lem.level >= level && !isLoaded(level, lem.getID());
  }

  void MultiSATConsecutionChecker::addLemmaToManager(const Lemma & lem, SAT::Manager & manager) {
    const Cube & cube = lem.getCube();
    Clause cls;
    Expr::complement(ev, cube, cls);
    manager.add(cls);
  }

  /*
   * Get the manager for the given level.
   */
  SAT::Manager & MultiSATConsecutionChecker::getManager(int level) {
    auto it = levels.find(level);
    if (it == levels.end()) {
      initSAT(level);
      it = levels.find(level);
    }

    assert(it != levels.end());
    const SATLevel & sat_level = it->second;
    return *sat_level.manager;
  }

  SAT::Manager::View & MultiSATConsecutionChecker::getView(int level) {
    auto it = levels.find(level);
    if (it == levels.end()) {
      initSAT(level);
      it = levels.find(level);
    }

    assert(it != levels.end());
    const SATLevel & sat_level = it->second;
    return *sat_level.view;
  }

  bool MultiSATConsecutionChecker::doRenewSAT() {
    levels.clear();

    return false;
  }

  void MultiSATConsecutionChecker::doLoadLemma(const Lemma & lem) {
    for (auto it = levels.begin(); it != levels.end(); ++it) {
      int manager_level = it->first;
      const SATLevel & sat_level = it->second;
      if (safeToAdd(lem, manager_level)) {
        SAT::Manager & manager = *sat_level.manager;
        addLemmaToManager(lem, manager);
        setLoaded(manager_level, lem.getID());
      }
    }
  }

  bool MultiSATConsecutionChecker::doConsecution(ConsecutionOpts & opts) {
    assert(opts.support_set == NULL);
    assert(opts.level >= 0);
    assert(opts.cube || opts.unprimed_cube || opts.extra_assumps);
    assert(!(opts.cube == NULL && opts.reduced != NULL));
    assert(!opts.filter);

    int level = opts.level;
    int dec_budget = opts.dec_budget;
    int * conf = nullptr;

    SAT::Manager::View & sat_view = getView(level);

    Expr::IDVector assumps, cassumps;
    assumps = defaultAssumptions(opts);
    cassumps = defaultCriticalAssumptions(opts);

    SAT::GID gid = SAT::NULL_GID;
    if (opts.cube) {
      const Cube & cube = *opts.cube;

      Clause cc;
      Expr::complement(ev, cube, cc);
      gid = sat_view.newGID();
      sat_view.add(cc, gid);
    }

    bool is_sat = sat_view.sat(&assumps,
                               opts.assignment,
                               opts.reduced ? &cassumps : NULL,
                               SAT::NULL_GID,
                               false,
                               NULL,
                               NULL,
                               conf);

    if (dec_budget > opts.dec_budget && is_sat) {
      opts.timed_out = true;
    } else {
      opts.timed_out = false;
    }

    if (!is_sat && opts.reduced) {
      assert(opts.cube);
      reduceCube(*opts.cube, *opts.reduced, cassumps);
    }

    if (opts.cube) {
      assert(gid != SAT::NULL_GID);
      sat_view.remove(gid);
    }

    return !is_sat;
  }

  void ActivationMultiSATConsecutionChecker::addLemmaToManager(const Lemma & lem, SAT::Manager & manager) {
    const Cube & cube = lem.getCube();
    Clause cls;
    Expr::complement(ev, cube, cls);

    ID act = activationLit(lem.getID());
    cls.push_back(act);

    manager.add(cls);
  }

  bool ActivationMultiSATConsecutionChecker::doConsecution(ConsecutionOpts & opts) {
    assert(opts.level >= 0);
    assert(opts.cube || opts.unprimed_cube || opts.extra_assumps);
    assert(!(opts.cube == NULL && opts.reduced != NULL));
    // Not implemented
    if (opts.dec_budget > 0) {
      throw std::logic_error("ActivationMultiSATConsecutionChecker support for budgets is not implemented");
    }


    bool do_support = (opts.support_set != NULL);

    int level = opts.level;
    SAT::Manager::View & sat_view = getView(level);

    Expr::IDVector assumps, cassumps;
    assumps = defaultAssumptions(opts);
    cassumps = defaultCriticalAssumptions(opts);

    SAT::GID gid = SAT::NULL_GID;
    if (opts.cube) {
      const Cube & cube = *opts.cube;

      Clause cc;
      Expr::complement(ev, cube, cc);
      gid = sat_view.newGID();
      sat_view.add(cc, gid);
    }

    for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
      if (lem.level >= level) {
        if (opts.filter && !opts.filter(lem)) {
          continue;
        }

        if (isFilteredOut(lem)) {
          continue;
        }

        assert(isLoaded(level, lem.getID()));

        ID act = activationLit(lem.getID());
        ID nact = ev.apply(Expr::Not, act);
        assumps.push_back(nact);
        if (do_support) {
          cassumps.push_back(nact);
        }
      }
    }

    bool is_sat = sat_view.sat(&assumps,
                               opts.assignment,
                               opts.reduced || do_support ? &cassumps : NULL,
                               SAT::NULL_GID,
                               false,
                               NULL,
                               NULL);

    if (!is_sat && opts.reduced) {
      assert(opts.cube);
      reduceCube(*opts.cube, *opts.reduced, cassumps);
    }

    if (!is_sat && do_support) {
      *opts.support_set = computeSupport(cassumps);
    }

    if (opts.cube) {
      assert(gid != SAT::NULL_GID);
      sat_view.remove(gid);
    }

    return !is_sat;
  }

  std::set<CubeID> ActivationMultiSATConsecutionChecker::computeSupport(const Cube & crits) const {
    std::set<CubeID> support;
    for(auto it = crits.begin(); it != crits.end(); ++it) {
      ID crit = *it;

      if (isActivationLit(crit)) {
        CubeID support_id = (CubeID) inverseActivationLit(crit);
        support.insert(support_id);
      }
    }

    return support;
  }

  /*
   * This checker can tolerate deletion except in the case of F_infinity, and
   * even then it's fine if the deleted lemma is subsumed by another infinity
   * lemma
   */
  void ActivationMultiSATConsecutionChecker::lemmaDeleted(const Lemma & lem) {
#ifdef DEBUG
    if (lem.level == INT_MAX && !isFilteredOut(lem)) {
      // the lemma must be subsumed by another infinity lemma for this to be a
      // safe operation
      const Frame & finf = inductive_trace.getInfFrame();
      bool found = false;
      for (CubeID id : finf) {
        const Cube & cube = inductive_trace.getCube(id);
        if (subsumes(lem.getCube(), cube) && isLoaded(INT_MAX, id)) {
          found = true;
          break;
        }
      }
      assert(found);
    }
#else
    (void) lem;
#endif
  }


}

