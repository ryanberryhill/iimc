#include "UMCEngine.h"
#include "Random.h"

namespace UMC {

  ProofObligation & newPooledObligation(ObligationPool & p,
                                        const Cube & cube,
                                        int level,
                                        ProofObligation * parent = NULL,
                                        ProofKind type = MUST_PROOF) {
    p.push_back(ProofObligation(cube, level, parent, type));
    return p.back();
  }

  ProofObligation & newPooledObligation(ObligationPool & p,
                                        const ProofObligation & other) {
    p.push_back(ProofObligation(other));
    return p.back();
  }

  unsigned luby(unsigned n)
  {
    for (unsigned k = 1; k < 32; ++k)
    {
      if (n == (1u << k) - 1)
      {
        return 1 << (k - 1);
      }
    }

    for (unsigned k = 1; ; ++k)
    {
      if ((1u << (k - 1) <= n) && (n < (1u << k) - 1))
      {
        return luby(n - (1 << (k - 1)) + 1);
      }
    }
  }

  unsigned resetFactor(unsigned n)
  {
    return luby(n);
    // A simple sequence where rf(n) > rf(n - 1) for all n > 0 and
    // that grows slower than 2^n.
    //if (n < 4) { return n; }
    //else { return (unsigned) pow(2, (double) n / 2); }
  }

  UMCEngine::UMCEngine(Model & m, UMCOptions o) :
                                           ev(m.newView()),
                                           logger(m.verbosity()),
                                           m(m),
                                           opts(o),
                                           current_level(0),
                                           num_resets(0),
                                           lemmas_learned_since_reset(0),
                                           inductive_trace(opts, stats),
                                           initiation_checker(m, *ev),
                                           gs(m, stats, logger, opts, inductive_trace, initiation_checker, *ev)
  {
    ev->begin_local();
    initCircuitData();
    // prepare() is virtual, but we only want to call UMCEngine::prepare,
    // so this is fine (calling this virtual function in the constructor)
    prepare();
  }

  /*
   * Default IC3-style behavior. Indicate a counter-example if the obligation
   * is at level 0. Support only must-proofs.
   */
  std::pair<bool, bool> UMCEngine::beforeBlock(ProofObligation & po) {
    assert(po.type == MUST_PROOF);
    if (po.level == 0) {
      po.cex_state = initCube();
      return std::make_pair(true, true);
    }
    return std::make_pair(false, false);
  }

  /*
   * Default IC3-style behavior. Re-enqueue the same CTI at the next level
   */
  void UMCEngine::onDischarge(ProofObligation & po, const Cube & t, int g) {
    (void) t;
    if (po.type == MAY_PROOF) {
      stats.may_success++;
    } else {
      stats.must_success++;
    }

    if (g < INT_MAX && (g + 1) < getLevel()) {
      if (options().reenqueue) {
        // Reinsert the original obligation at level g + 1
        po.level = g + 1;
        pushObligation(po);
      }
    }
  }

  /*
   * Default IC3-style behavior (though probably common to all solvers)
   * Add an obligation for the predecessor and re-enqueue the original.
   */
  void UMCEngine::onPredecessor(ProofObligation & po,
                                const Cube & inputs,
                                const Cube & pinputs,
                                const Cube & pred) {
    ProofObligation & next_po = newObligation(pred, po.level - 1, &po);
    next_po.type = po.type;
    next_po.inputs = inputs;

    // For counter-example generation sometimes its important to enforce the
    // primed inputs that relate to the state before the unsafe state.
    // In this case where the obligation is for !Bad, po.inputs will be empty,
    // so set them to the primed inputs from the child obligation (unpriming
    // them in the process).
    if (po.inputs.empty())
    {
        for (ID id : pinputs)
        {
            po.inputs.push_back(ev->unprime(id));
        }
    }

    pushObligation(next_po);
    pushObligation(po);
  }

  void UMCEngine::initCircuitData() {
    const ExprAttachment * eat = (const ExprAttachment *) model().constAttachment(Key::EXPR);

    state_vars.clear();
    input_vars.clear();
    state_vars.insert(eat->stateVars().begin(), eat->stateVars().end());
    input_vars.insert(eat->inputs().begin(), eat->inputs().end());

    init_cube = eat->initialConditions();

    // initially is separate from init cube to allow future support for
    // incrementality with different initial states
    initially.clear();
    initially.insert(init_cube.begin(), init_cube.end());
    stats.init_state_bits = initially.size();

    initiation_checker.setInit(initially);

    // Check for the case where there are constraints and they are a function
    // of primary inputs. In this case, lifting must be disabled
    if (opts.lift) {
      std::vector<ID> constraintFns = eat->constraintFns();
      // TODO handle lifting and constraints properly. For now, just disable
      // lifting when constraints are present
      std::set<ID> constraintVars;
      Expr::variables(*ev, constraintFns, constraintVars);
      for (ID var : constraintVars) {
        logger.terse() << pc({var}) << std::endl;
        if (eat->isInput(var)) {
          opts.lift = false;
          logger.terse() << "Disabling lifting due to input-dependent constraints" << std::endl;
          break;
        }
      }

      // We also can't handle hard constraints
      for (ID fn : constraintFns)
      {
        if (eat->isSoftConstraint(fn)) {
          //handleSoftConstraint(fn);
        } else {
          opts.lift = false;
          logger.terse() << "Disabling lifting due to hard constraints" << std::endl;
        }
      }
    }

    model().constRelease(eat);

    // Handle the absence of a COIAttachment gracefully by assuming all
    // registers are in the COI
    coi_latches.clear();
    const COIAttachment * cat = (const COIAttachment *) model().constAttachment(Key::COI);
    if(cat) {
      COI coi = cat->coi();

      COI::range latch_range = coi.cCOI();
      coi_latches.insert(latch_range.first, latch_range.second);

      model().constRelease(cat);
    } else {
      coi_latches.insert(state_vars.begin(), state_vars.end());
    }
  }

  ID UMCEngine::getNPI() const {
    const ExprAttachment * eat = (const ExprAttachment *) model().constAttachment(Key::EXPR);

    ID npi = eat->outputFnOf(eat->outputs()[0]);
    Cube cube;
    Expr::conjuncts(*ev, npi, cube);
    npi = ev->apply(Expr::And, cube);

    model().constRelease(eat);

    return npi;
  }

  void UMCEngine::prime(Expr::IDVector & vec) const {
    std::transform(vec.begin(), vec.end(), vec.begin(), [&](ID x){ return ev->prime(x); });
  }

  void UMCEngine::printStats() const {
    const Frame & finf = inductive_trace.getInfFrame();
    stats.proof_size = finf.size();

    for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
      if (lem.bad) {
        stats.bad_lemmas++;
      }

      if (lem.ugly) {
        stats.ugly_lemmas++;
      }

      stats.total_lemmas++;
    }

    stats.total_lemmas += finf.size();
    stats.print();
  }

  bool UMCEngine::initiation(const Cube & cube) const {
    return initiation_checker.initiation(cube);
  }

  void UMCEngine::logObligation(const ProofObligation & po) const {
    logger.logorrheic() << (po.type == MUST_PROOF ? "Must" : "May")
                        << " proof obligation at level " << po.level
                        << " and depth " << po.depth
                        << " for cube " << pc(po.cube)
                        << std::endl;
  }

  void UMCEngine::logAddCube(const std::string & prefix,
                              const Lemma & lem,
                              std::ostream & stream) const
  {
    const Cube & cube = lem.getCube();
    int lv = lem.level;
    CubeID id = inductive_trace.getID(cube);
    std::string lv_string = (lv == INT_MAX ? "inf" : std::to_string(lv));
    stream << prefix << " " << lv_string << ": "
           << pc(cube) << " [" << id << "]"
           << std::endl;
  }

  std::pair<Cube, int> UMCEngine::syntacticBlock(const ProofObligation & po) {
    AutoTimer auto_timer(stats.syn_check_time);
    const Cube & s = po.cube;
    int k = po.level;
    assert(k <= getLevel());

    // Syntactically check if s is blocked by a cube in one of the frames
    // Can't use getActiveLemmas here, need to sort by level
    const Frame & inf_frame = inductive_trace.getInfFrame();
    for (auto it = inf_frame.begin(); it != inf_frame.end(); it++) {
      const Cube & c = inductive_trace.getCube(*it);
#ifdef DEBUG
        const Lemma & lem = getLemma(c);
        assert(lem.level == INT_MAX);
#endif
      if (subsumes(s, c)) {
        return std::make_pair(c, INT_MAX);
      }
    }

    for (int i = inductive_trace.getMaxFrame(); i >= k; i--) {
      const Frame fi = inductive_trace.getFrame(i);
      for (auto it = fi.begin(); it != fi.end(); it++) {
        const Cube & c = inductive_trace.getCube(*it);
#ifdef DEBUG
        const Lemma & lem = getLemma(c);
        assert(lem.level == i);
#endif
        if (subsumes(s, c)) {
          return std::make_pair(c, i);
        }
      }
    }

    return std::make_pair(Cube(), -1);
  }

  /*
   * Initialize the SAT::Assignment with latches in the COI and inputs and
   * the primes thereof
   */
  void UMCEngine::initializeAsgn(SAT::Assignment & asgn) const {
    asgn.clear();

    // Include state, primed state, input, primed input
    for (ID id : coi_latches) {
      asgn.insert(SAT::Assignment::value_type(id, SAT::Unknown));
      asgn.insert(SAT::Assignment::value_type(ev->prime(id), SAT::Unknown));
    }
    for (ID id : input_vars) {
      asgn.insert(SAT::Assignment::value_type(id, SAT::Unknown));
      asgn.insert(SAT::Assignment::value_type(ev->prime(id), SAT::Unknown));
    }
  }

  ID UMCEngine::parseSATResult(SAT::AssignVal val, ID lit) const {
    return val == SAT::False ? ev->apply(Expr::Not, lit) : lit;
  }

  /*
   * This function can be called after a satisified sat query. It gets the state,
   * inputs, and primed inputs from the satisfying assignment which are used to
   * construct the counterexample trace.
   */
  void UMCEngine::getCubesFromAsgn(const SAT::Assignment & asgn,
                                   Cube * cube,
                                   Cube * input_cube,
                                   Cube * p_input_cube,
                                   Cube * p_state) const
  {
    for (SAT::Assignment::const_iterator it = asgn.begin(); it != asgn.end(); ++it) {
      if (it->second == SAT::Unknown) { continue; }
      ID lit = it->first;
      SAT::AssignVal val = it->second;

      if (ev->nprimes(lit) == 0) {
        if (input_cube && isInput(lit)) {
          // Unprimed input - do the obvious
          input_cube->push_back(parseSATResult(val, lit));
        } else if (cube && inCOI(lit)) {
          // unprimed state - include if it's in the COI
          // This is used for constructing lemmas, so we only need the COI
          cube->push_back(parseSATResult(val, lit));
        }
      } else {
        assert(ev->nprimes(lit) == 1);
        ID unprimed_lit = ev->unprime(lit);
        if (p_input_cube && isInput(unprimed_lit)) {
          // Primed input - unprime and do the obvious
          p_input_cube->push_back(parseSATResult(val, lit));
        } else if (p_state && isStateVar(unprimed_lit)) {
          // primed state - do not unprime, and include regardless of COI.
          // This is used for constructing counterexamples, we want the full state
          p_state->push_back(parseSATResult(val, unprimed_lit));
        }
      }
    }
  }

  /*
   * If s is successfully blocked, returns (t,g) where t is a cube such that
   * !t blocks s, and g is the level to which that !t holds.
   * If s cannot be blocked, returns a predecessor cube of s and g = k-1.
   * Guarantees that the returned cube is sorted
   */
  std::pair<Cube, int> UMCEngine::block(ProofObligation & po,
                                        Cube * inputs,
                                        Cube * pinputs,
                                        Cube * concrete_state)
  {
    const Cube & s = po.cube;
    int k = po.level;
    logger.logorrheic() << "block, level " << k << ", cube " << pc(s) << std::endl;
    assert(k <= getLevel());

    std::pair<Cube, int> syntactic = syntacticBlock(po);
    if (!syntactic.first.empty()) {
      const Cube & c = syntactic.first;
#ifdef DEBUG
      assert(std::is_sorted(c.begin(), c.end()));
#endif
      int i = syntactic.second;
      assert(i >= 0);
      // Note: it's important to add the cube, even though it's subsumed.
      // The subsuming lemma might be a bad lemma, and this one might not.
      // We don't do it in the case of F_inf because obviously the
      // subsuming lemma is good and not bad
      if (s != c && i < INT_MAX) {
        addCube(s, i);
      }

      stats.syntactic_block_success++;
      return syntactic;
    }

    stats.syntactic_block_fail++;

    std::pair<Cube, int> post_syn = afterSyntacticCheck(po);
    if (post_syn.second >= 0) {
#ifdef DEBUG
      assert(std::is_sorted(post_syn.first.begin(), post_syn.first.end()));
#endif
      lemmas_learned_since_reset++;
      addCube(post_syn.first, post_syn.second);
      return post_syn;
    }

    SAT::Assignment asgn;
    initializeAsgn(asgn);
    bool cons = consecution(s, k - 1, &asgn);
    logger.logorrheic() << "cons: " << cons << std::endl;

    if (!cons) {
      // Extract and return predecessor state t and optionally concrete_state
      // (the concrete s-state involved in the assignment)
      // pinp = primed inputs (forced by s)
      Cube t, local_inputs, local_pinputs;
      Cube & inp = inputs ? *inputs : local_inputs;
      Cube & pinp = pinputs ? *pinputs : local_pinputs;

      getCubesFromAsgn(asgn, &t, &inp, &pinp, concrete_state);
      std::sort(t.begin(), t.end());
      // Generalize the predecessor via lifting
      if (options().lift) {
        lift(t, inp, pinp, s);
      }
      assert(!t.empty());
      std::sort(t.begin(), t.end());
      return make_pair(t, k - 1);
    } else {
      Cube t(s);
      // Generalize t
      int g = k;
      if (!po.from_sg && t != badCube()) {
        g = generalize(k - 1, inductive_trace.getMaxFrame(), t);
#ifdef DEBUG
        assert(consecution(t, g < INT_MAX ? g - 1 : INT_MAX));
#endif
      }

      stats.cube_size_total += (int) t.size();
      stats.cube_size_cnt++;
      assert(g == INT_MAX || g <= (inductive_trace.getMaxFrame() + 1));
      lemmas_learned_since_reset++;
      addCube(t, g);
      assert(!t.empty());
      std::sort(t.begin(), t.end());
      return make_pair(t, g);
    }
  }

  const Lemma & UMCEngine::getActiveLemma(const Cube & cube) const {
    assert(isActiveLemma(cube));
    return inductive_trace.getActiveLemma(cube);
  }

  const Lemma & UMCEngine::getActiveLemma(CubeID id) const {
    return inductive_trace.getActiveLemma(id);
  }

  const Lemma & UMCEngine::getLemma(const Cube & cube) const {
    assert(isKnownLemma(cube));
    return inductive_trace.getLemma(cube);
  }

  const Lemma & UMCEngine::getLemma(CubeID id) const {
    return inductive_trace.getLemma(id);
  }

  bool UMCEngine::isKnownLemma(CubeID id) const {
    return inductive_trace.isKnown(id);
  }

  bool UMCEngine::isKnownLemma(const Cube & cube) const {
    return inductive_trace.isKnown(cube);
  }

  bool UMCEngine::isActiveLemma(CubeID id) const {
    return inductive_trace.isActive(id);
  }

  bool UMCEngine::isActiveLemma(const Cube & cube) const {
    return inductive_trace.isActive(cube);
  }

  bool UMCEngine::isDeletedLemma(CubeID id) const {
    return inductive_trace.isDeleted(id);
  }

  bool UMCEngine::isDeletedLemma(const Cube & cube) const {
    return inductive_trace.isDeleted(cube);
  }

  /*
   * Get a cube representing the property lemma
   */
  Cube UMCEngine::badCube() const {
    Cube bad;
    bad.push_back(badVar());
    return bad;
  }

  /*
   * Function that can be called between incremental runs to reset any needed
   * state. Currently, the entire trace is cleared so it's not very
   * incremental.
   */
  void UMCEngine::reset(UMCOptions * new_opts) {
    cleanup();
    prepare(new_opts);
  }

  void UMCEngine::cleanup() {
    inductive_trace.clear();
  }

  void UMCEngine::prepare(UMCOptions * new_opts) {
    logger.setVerbosity(model().verbosity());
    if (new_opts) {
      setOptions(*new_opts);
    }

    for (ID id : initCube()) {
      Cube cube;
      cube.push_back(ev->apply(Expr::Not, id));
      addCube(cube, 0);
    }
  }

  void UMCEngine::deleteLemma(const CubeID id) {
    inductive_trace.deleteLemma(id);
    onDeleteLemma(id);
  }

  /*
   * Check if the problem is trivial.  May return a value indicating success or
   * failure if the problem is trivial.
   */
  ReturnValue UMCEngine::checkTrivial()
  {
    logger.informative() << "Starting checkTrivial" << std::endl;

    ReturnValue trivial_cexrv(MC::CEX);
    trivial_cexrv.cex.push_back(Transition(initCube(), Cube()));

    // Check for the case where the output is a constant
    ID npi = getNPI();
    if (npi == ev->bfalse()) {
      logger.informative() << "The property succeeds trivially." << std::endl;
      return ReturnValue(MC::Proof);
    }
    if (npi == ev->btrue()) {
      logger.informative() << "The property fails trivially." << std::endl;
      return trivial_cexrv;
    }

    return ReturnValue(MC::Unknown);
  }

  void UMCEngine::updateReachabilityBound(int k) {
    auto rat = m.attachment<RchAttachment>(Key::RCH);
    rat->updateCexLowerBound(k, getName());
    m.release(rat);
  }

  ReturnValue UMCEngine::prove()
  {
#ifdef DEBUG
    for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
      assert(!lem.getCube().empty());
      if (lem.level == 0) { continue; }
      assert(consecution(lem.getCube(), lem.level - (lem.level == INT_MAX ? 0 : 1)));
    }
#endif
    Cube bad_cube = badCube();
    ReturnValue rv = ReturnValue(MC::Unknown);
    logger.informative() << "Trying to block cube " << pc(bad_cube) << std::endl;

    if (checkInitial(bad_cube)) {
      rv.returnType = MC::CEX;
      Cube inputs;
      rv.cex.push_back(Transition(initCube(), inputs));
      return rv;
    }

    updateReachabilityBound(1);

    // Initial states are not bad, so add the cube here
    addCube(bad_cube, 0);
    const Lemma & bad_lemma = getActiveLemma(bad_cube);

    // Main loop - block the bad states at each level until a proof is found
    setLevel(0);
    while (true) {
      // Reset the counter for number of resets at each level
      num_resets = 0;
      lemmas_learned_since_reset = 0;
      incrementLevel();
      if (bad_lemma.level > getLevel() && bad_lemma.level < INT_MAX) {
        setLevel(bad_lemma.level);
      }

      int k = getLevel();

      logger.informative() << "\nLevel " << k << std::endl;
      // In the case of multiple calls, we'll report the highest level reached
      stats.level = std::max(stats.level, k);

      clearObligations();
      onBeginLevel(k);
      ReturnValue block_rv = proveBounded(k);
      assert(block_rv.returnType != MC::Unknown);

      if (block_rv.returnType == MC::CEX) {
        logger.informative() << "Counterexample of length "
                             << block_rv.cex.size()
                             << " found at level " << k << std::endl;
        return block_rv;
      }

      // Proven at k, report it externally
      updateReachabilityBound(k + 1);

#ifdef DEBUG
      for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
        assert(!lem.getCube().empty());
        if (lem.level == 0) { continue; }
        assert(consecution(lem.getCube(), lem.level - (lem.level == INT_MAX ? 0 : 1)));
      }
#endif

      if (options().reduce_inf) {
        reduceFinf();
      }

#ifdef DEBUG
      renew();
      for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
        assert(!lem.getCube().empty());
        if (lem.level == 0) { continue; }
        assert(consecution(lem.getCube(), lem.level - (lem.level == INT_MAX ? 0 : 1)));
      }
#endif

      if (options().subsumption_reduce) {
        reduceFrames();
      }

#ifdef DEBUG
      renew();
      for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
        assert(!lem.getCube().empty());
        if (lem.level == 0) { continue; }
        assert(consecution(lem.getCube(), lem.level - (lem.level == INT_MAX ? 0 : 1)));
      }
#endif

      pushClauses();
      renew();

#ifdef DEBUG
      for (const Lemma & lem : inductive_trace.getActiveLemmas()) {
        assert(!lem.getCube().empty());
        if (lem.level == 0) { continue; }
        int level = lem.level - (lem.level == INT_MAX ? 0 : 1);
        assert(consecution(lem.getCube(), level));
      }
#endif

      if (proofFound()) {
        rv.returnType = MC::Proof;
        onProofFound(rv.proof);
        return rv;
      }
    }

    return rv;
  }

  /*
   * Try to block bad_cube at level k.
   */
  ReturnValue UMCEngine::proveBounded(int k)
  {
    Cube bad_cube = badCube();
    ProofObligation & bad_obl = newObligation(bad_cube, k, NULL);
    pushObligation(bad_obl);

    while (!obligationQueueEmpty()) {
      ProofObligation & po = popObligation();
      assert(!po.cube.empty());

      if (po.failed) {
        assert(po.type != MUST_PROOF);
        continue;
      }

      logObligation(po);

      int reset_threshold = INT_MAX;
      if (options().clear_queue_threshold < INT_MAX)
      {
        reset_threshold = resetFactor(num_resets + 1) * options().clear_queue_threshold;
      }

      if (numObligations() > reset_threshold && lemmas_learned_since_reset > 0) {
        logger.verbose() << "Clearing the queue due to too many obligations" << std::endl;
        num_resets++;
        stats.resets++;

        lemmas_learned_since_reset = 0;
        clearObligations();
        renew();
        pushObligation(newObligation(bad_cube, k, NULL));
        continue;
      }

      // Time the obligation in the appropriate bucket
      double & time_bucket = (po.type == MUST_PROOF) ? stats.must_time : stats.may_time;
      AutoTimer auto_timer(time_bucket);

      bool handled = false;
      bool cex_found = false;
      std::tie(handled, cex_found) = beforeBlock(po);

      if (cex_found) {
        assert(handled);
        return buildCex(po);
      } else if (handled) {
        continue;
      }

      Cube inputs, pinputs, cex_state;
      Cube t;
      int g;
      std::tie(t, g) = block(po, &inputs, &pinputs, &cex_state);
      assert(!t.empty());

      if (g != po.level - 1) {
        // The obligation's CTI is blocked by ~t
        onDischarge(po, t, g);
      }
      else {
        // t is a predecessor of the obligation's CTI
        po.cex_state = cex_state;
        onPredecessor(po, inputs, pinputs, t);
      }
    }

    return ReturnValue(MC::Proof);
  }


  /*
   * Called when a proof is discovered. The default is to set the proof to
   * F_inf. However, other things are possible, e.g., doing proof minimization
   * or in the case of vanilla IC3 where no F_inf exists, using the fixpoint
   */
  void UMCEngine::onProofFound(std::vector<Cube> & proof) {
    proof.clear();
    const Frame & inf_frame = inductive_trace.getInfFrame();
    for (auto it = inf_frame.begin(); it != inf_frame.end(); it++) {
      Clause cls;
      const Cube & cube = inductive_trace.getCube(*it);
      if (cube != badCube()) {
        Expr::complement(*ev, cube, cls);
        proof.push_back(cls);
      }
    }
  }

  /*
   * Primary interface to the solver. Requires no external setup other than
   * constructing the solver object.
   */
  ReturnValue UMCEngine::solve() {
    ReturnValue rv;
    {
      AutoTimer auto_timer(stats.solve_time);
      rv = checkTrivial();

      if (rv.returnType == MC::Unknown) {
        rv = prove();
      }

      onEndSolve();
    }

    if (options().print_stats) {
      printStats();
    }

    return rv;
  }

  /*
   * This is a universal way to check for a proof, though other
   * solvers could implement alternatives.
   */
  bool UMCEngine::proofFound() {
    // A proof is found if F_inf => ~bad
    return !checkInf(badCube());
  }

  /*
   * Build a counter-example for a failed obligation. Can be overridden to
   * do things like e.g., handling reachable states in Quip
   */
  ReturnValue UMCEngine::buildCex(ProofObligation & obl) {
    ReturnValue rv = ReturnValue(MC::CEX);

    ProofObligation * po = &obl;
    while (po) {
      rv.cex.push_back(Transition(po->cex_state, po->inputs));
      po = po->parent;
    }
    return rv;
  }

  void UMCEngine::deleteSubsumedLemma(const Lemma & lem) {
    inductive_trace.silentlyDeleteLemma(lem);
  }

  void UMCEngine::deleteSubsumedLemma(CubeID id) {
    inductive_trace.silentlyDeleteLemma(id);
  }

  /*
   * Reduce the cubes in F_inf. For each one, run consecution against level
   * infinity and reduce using the critical assumptions
   */
  void UMCEngine::reduceFinf() {
    AutoTimer auto_timer(stats.reduce_inf_time);
    logger.logorrheic() << "Reducing absolute invariants" << std::endl;
    bool steady = false;
    while (!steady) {
      steady = true;
      Frame inf_frame = inductive_trace.copyInfFrame();
      for (CubeID id : inf_frame) {
        const Lemma & lem = getActiveLemma(id);

        const Cube & cube = lem.getCube();
        Cube reduced;
        bool ind = consecution(cube, INT_MAX, NULL, &reduced);
        assert(ind);
        std::sort(reduced.begin(), reduced.end());
#ifdef DEBUG
        assert(subsumes(cube, reduced));
        assert(!reduced.empty());
        assert(consecution(reduced, INT_MAX));
#endif

        assert(reduced.size() <= cube.size());
        bool success = false;
        if (reduced.size() < cube.size()) {
          deleteSubsumedLemma(id);
          if (isActiveLemma(reduced)) {
            const Lemma & known = getActiveLemma(reduced);
            // If we already know the reduced lemma at level infinity, we
            // shouldn't count this as a reduction
            success = (known.level < INT_MAX);
          } else {
            success = true;
          }

          if (success) {
            addCube(reduced, INT_MAX);
            stats.inf_cubes_reduced++;
            steady = false;
          }
        }
      }
    }
  }

  void UMCEngine::deleteAllSubsumedBy(CubeID id) {
    const Lemma & lem = getActiveLemma(id);
    deleteAllSubsumedBy(lem);
  }

  void UMCEngine::deleteAllSubsumedBy(const Lemma & lem) {
    std::vector<CubeID> subsumed = inductive_trace.getCubesSubsumedBy(lem);
    for (CubeID subsumed_cube_id : subsumed) {
      if (isActiveLemma(subsumed_cube_id)) {
        const Lemma & subsumed = getLemma(subsumed_cube_id);
        if (lem.getID() != subsumed.getID()) {
          assert(lem.level >= subsumed.level);
          logger.logorrheic() << "Deleting cube (" << pc(subsumed.getCube())
                              << ") subsumed by (" << pc(lem.getCube())
                              << ")" << std::endl;
          deleteSubsumedLemma(subsumed_cube_id);
        }
#ifdef DEBUG
        assert(subsumes(subsumed.getCube(), lem.getCube()));
#endif
      }
    }

  }

  /*
   * Reduce the inductive trace using subsumption
   */
  void UMCEngine::reduceFrames() {
    AutoTimer timer(stats.reduce_frames_time);
    for (int i = inductive_trace.getMaxFrame(); i >= 0; --i) {
      Frame fi = inductive_trace.copyFrame(i);
      for (CubeID id : fi) {
        if (isActiveLemma(id)) {
          const Lemma & lem = getActiveLemma(id);
          deleteAllSubsumedBy(lem);
        }
      }
    }
  }

  /*
   * Called when a lemma is successfully pushed. level is the destination level
   * and reduced is the reduced version of the lemma's cube. reduced should
   * be inductive relative to (level - 1).
   */
  void UMCEngine::lemmaPushed(const Lemma & lem, int level, const Cube & reduced) {
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
      if (isActiveLemma(reduced)) {
        const Lemma & red_lem = getActiveLemma(reduced);
        if (red_lem.level < level) {
          addCube(reduced, level);
          deleteSubsumedLemma(lem);
        }
      } else {
        addCube(reduced, level);
        deleteSubsumedLemma(lem);
      }
    }
  }

  /*
   * Generic implementation of pushClauses with various hooks. This matches
   * a Quip push more than an IC3-style one.
   */
  void UMCEngine::pushClauses()
  {
    logger.verbose() << "\nStarting pushClauses" << std::endl;
    AutoTimer auto_timer(stats.push_time);

    for (int k = 1; k <= inductive_trace.getMaxFrame(); k++) {
      int push_count = 0;

      // We need to copy the frame because we'll be modifying it
      const Frame fk = inductive_trace.copyFrame(k);
      int fk_size = fk.size();
      for (auto it = fk.begin(); it != fk.end(); ++it) {
        const Lemma & lem = getActiveLemma(*it);
        assert(lem.level >= k);

        if (lem.level > k) {
          // The lemma may have been pushed already by reduction (we tried to
          // push a different lemma that was reduced to this one). Count this
          // lemma as having been pushed as well (because it was earlier)
          push_count++;
          continue;
        }

        bool skip = !beforeTryPropagate(lem);
        if (skip) {
          continue;
        }

        Cube reduced;
        int result = tryPropagate(lem, reduced);
        assert(result >= k);
        if (result > k) {
          push_count++;
          // Reduced can come back empty, meaning we didn't need
          // c to make the problem unsat
          if (reduced.empty()) { reduced = lem.getCube(); }
          lemmaPushed(lem, result, reduced);
        }
      }

      if (push_count == fk_size) {
        assert(inductive_trace.getFrame(k).empty());
        logger.logorrheic() << "Found inductive frame at k = " << k << std::endl;
        // Fk is fully inductive, so push all cubes in F_k to infinity. With
        // the delta encoding, this means frame(k) to frame(max). frame(k)
        // should already be empty though
        Frame inductive_frame;
        for (int i = k + 1; i <= inductive_trace.getMaxFrame(); i++) {
          const Frame & fi = inductive_trace.getFrame(i);
          inductive_frame.insert(fi.begin(), fi.end());
        }

        for (CubeID id : inductive_frame) {
          addCubeByID(id, INT_MAX);
        }

#ifdef DEBUG
        for (int i = k; i <= inductive_trace.getMaxFrame(); i++) {
          assert(inductive_trace.getFrame(i).empty());
        }

        for (CubeID id : inductive_frame) {
          const Cube & cube = getActiveLemma(id).getCube();
          assert(consecution(cube, INT_MAX));
        }
#endif

        break;
      }
    }
  }

  /*
   * Simplest implementation possible. Try to push one level only.
   */
  int UMCEngine::tryPropagate(const Lemma & lem, Cube & reduced) {
    const Cube & c = lem.getCube();
    int level = lem.level;
    assert(level < INT_MAX);
    stats.cons_from_prop_cls++;
    if (consecution(c, level, NULL, &reduced)) {
      return level + 1;
    }
    return level;
  }

  /*
   * Add a lemma for the given cube, whatever that means. This could mean
   * creating a new lemma, promoting an existing one, or reviving a deleted one
   */
  void UMCEngine::addCube(const Cube & cube, int lv)
  {
    assert(!cube.empty());
    Cube cube_sorted(cube);
    sort(cube_sorted.begin(), cube_sorted.end());

    bool was_active = isActiveLemma(cube_sorted);
    const Lemma & lem = inductive_trace.addCube(cube, lv);

    std::string log_string;
    if (was_active) {
      onAddKnownCube(lem, lem.level);
      log_string = "To";
    } else {
      onAddNewCube(lem, lem.level);
      log_string = "At";
    }

    logAddCube(log_string, lem, logger.verbose());
    onAddCube(lem, lv);
  }

  bool UMCEngine::obligationQueueEmpty() const {
    return obligations.empty();
  }

  ProofObligation & UMCEngine::popObligation() {
    ProofObligation & po = obligations.top();
    obligations.pop();
    return po;
  }

  void UMCEngine::pushObligation(ProofObligation & po) {
    if (po.type == MUST_PROOF) {
      stats.recordStat(stats.must_proof_dist, po.level);
    } else {
      assert(po.type == MAY_PROOF);
      stats.recordStat(stats.may_proof_dist, po.level);
    }
    obligations.push(po);
  }

  ProofObligation & UMCEngine::newObligation(const Cube & c, int k, ProofObligation * parent) {
    return newPooledObligation(obligation_pool, c, k, parent);
  }

  ProofObligation & UMCEngine::copyObligation(ProofObligation & orig) {
    return newPooledObligation(obligation_pool, orig);
  }

  int UMCEngine::numObligations() const {
    return obligations.size();
  }

  void UMCEngine::clearObligations() {
    obligations = ObligationQueue();
    obligation_pool.clear();
    onClearObligations();
  }

  ConsecutionChecker * UMCEngine::checkerFromString(const std::string & type) const {
    if (type == "level") {
      return checker<LevelBasedConsecutionChecker>();
    } else if (type == "multi") {
      return checker<MultiSATConsecutionChecker>();
    } else if (type == "activation") {
      return checker<ActivationBasedConsecutionChecker>();
    } else if (type == "activationmulti") {
      return checker<ActivationMultiSATConsecutionChecker>();
    } else {
      std::string msg = type + " is not a recognized consecution strategy";
      throw std::invalid_argument(msg);
    }
  }

  Generalizer * UMCEngine::generalizerFromString(const std::string & type, ConsecutionChecker & cons) {
    if (type == "down") {
      return generalizer<Generalizer>(cons, opts.gen_random);
    } else if (type == "iter") {
      return generalizer<IterativeGeneralizer>(cons, opts.gen_random);
    } else {
      std::string msg = type + " is not a recognized generalization strategy";
      throw std::invalid_argument(msg);
    }
  }


}

