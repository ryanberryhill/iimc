#include "Truss.h"

namespace UMC {

  TrussSolver::TrussSolver(Model & m, UMCOptions o) :
    QuipSolver(m, o),
    support_checker (checkerFromString(options().support_cons)),
    support_graph   (new SupportGraph(inductive_trace, logger))
  {
    trussPrepare();
  }

  /*
   * Cleanup function for things that should be cleaned up between incremental
   * runs.  Things that should persist across incremental runs should be
   * cleared in the destructor
   */
  void TrussSolver::cleanup() {
    QuipSolver::cleanup();
    trussCleanup();
  }

  void TrussSolver::trussCleanup() {
  }

  /*
   * Prepare function to set up things that are unique to a particular
   * incremental run.  Things that last across incremental runs should be set
   * up in the constructor.
   */
  void TrussSolver::prepare(UMCOptions * new_opts) {
    QuipSolver::prepare(new_opts);
    trussPrepare();
  }

  void TrussSolver::trussPrepare() {
    support_checker->setStrongFilter(no_bad_no_ugly);
    bool trivial = trussRenewSAT();
    assert(!trivial);
  }

  void TrussSolver::markUgly(const Cube & cube) {
    assert(isActiveLemma(cube));
    const Lemma & lem = getActiveLemma(cube);
    inductive_trace.markUgly(cube);
    if (!lem.ugly) {
      stats.ugly_marked++;
    }
  }

  void TrussSolver::unmarkUgly(const Cube & cube) {
    assert(isActiveLemma(cube));
    const Lemma & lem = getActiveLemma(cube);
    inductive_trace.unmarkUgly(cube);
    if (lem.ugly) {
      stats.ugly_unmarked++;
    }
  }

  /*
   * Checks if the lemma is acceptable. For now, acceptable means not bad
   * and not ugly, but we could easily consider other critera
   */
  bool TrussSolver::isAcceptable(const Cube & cube) const {
    CubeID id = inductive_trace.getID(cube);
    return isAcceptable(id);
  }

  bool TrussSolver::isAcceptable(CubeID id) const {
    const Lemma & lem = getLemma(id);
    return inductive_trace.isActive(id) && !lem.bad && (!lem.ugly || !options().ugly_lemmas);
  }

  /*
   * Returns true if and only if we know a support set for cube that
   * is acceptable. If cube is not a known lemma, returns false
   */
  bool TrussSolver::hasAcceptableSupport(const Cube & cube) const {
    if (!isActiveLemma(cube)) {
      return false;
    }

    bool has_support = support_graph->hasSupportSet(cube);
    if (!has_support) {
      return false;
    }

    auto support_range = support_graph->getInEdges(cube);
    for (auto it = support_range.first; it != support_range.second; ++it) {
      CubeID id = *it;
      if (!isAcceptable(id)) {
        return false;
      }
    }

    return true;
  }

  bool TrussSolver::hasBadSupport(const Cube & cube) const {
    if (!isActiveLemma(cube)) {
      return false;
    }

    bool has_support = support_graph->hasSupportSet(cube);
    if (!has_support) {
      return false;
    }

    auto support_range = support_graph->getInEdges(cube);
    for (auto it = support_range.first; it != support_range.second; ++it) {
      CubeID id = *it;
      if (getActiveLemma(id).bad) {
        return true;
      }
    }

    return false;
  }

  int TrussSolver::getSupportLevel(const Cube & cube) const {
    assert(isActiveLemma(cube));
    int lvl = getActiveLemma(cube).level;

    if(lvl < INT_MAX) {
      lvl -= 1;
    }

    return lvl;
  }

  /*
   * Tries to compute an acceptable (no blacklisted lemmas) support set.
   * Returns true if an acceptable support set was found, false otherwise
   */
  bool TrussSolver::computeAcceptableSupport(const Cube & cube, int lvl) {
    stats.support_calls++;
    AutoTimer auto_timer(stats.support_time);
    if(lvl < 0) {
      lvl = getSupportLevel(cube);
    }
    assert(lvl >= 0);
    bool cons = consecutionActivation(cube, lvl, NULL, NULL, CONSECUTION_ACCEPTABLE_SG);
    return cons;
  }

  void TrussSolver::computeSupport(const Cube & cube) {
    int lvl = getSupportLevel(cube);
    assert(lvl >= 0);
    computeSupport(cube, lvl);
  }

  /*
   * Computes the support set of the cube at the given level and stores it in
   * the support graph. Just a simple wrapper around consecution.
   */
  void TrussSolver::computeSupport(const Cube & cube, int lvl) {
    bool cons = consecutionActivation(cube, lvl, NULL, NULL, CONSECUTION_SG);
    assert(cons);
  }

  /*
   * Do consecution using the SAT manager with activation literals for each
   * individual clause. Update the support graph if consecution holds
   */
  bool TrussSolver::consecutionActivation(const Cube & c,
                                         int k,
                                         SAT::Assignment * asgn,
                                         Cube * reduced,
                                         ConsecutionType type) {
    bool do_support_graph = (type != CONSECUTION_NO_SG);
    bool acceptable_sg = (type == CONSECUTION_ACCEPTABLE_SG);
    assert(do_support_graph && acceptable_sg);

    // If the support graph demands SG on every consecution call, this
    // may not be a "real" lemma. However, we no longer support that behavior,
    // so just assert that it does not happen.
    assert(!(do_support_graph && !isActiveLemma(c)));

    bool cons = false;
    std::set<CubeID> support_set;

    ConsecutionOpts copts;
    copts.level = k;
    copts.cube = &c;
    copts.assignment = asgn;
    copts.reduced = reduced;

    if (do_support_graph) {
      copts.support_set = &support_set;
    }

    stats.consecution_calls++;
    cons = support_checker->consecution(copts);

    if (cons && do_support_graph) {
      assert(isKnownLemma(c));
      CubeID id = inductive_trace.getID(c);
      if (hasBadSupport(c)) {
        support_graph->deleteSupport(id);
      }
      support_graph->recordSupport(support_set, id);
    }

    return cons;
  }

  /*
   * First try to push using the supports. If that fails try to push to
   * infinity. If that fails, try to push one level only.
   */
  int TrussSolver::tryPropagate(const Lemma & lem, Cube & reduced) {
    //const Cube & c = lem.getCube();
    //int level = lem.level;
    //assert(level < INT_MAX);
    // TODO: fix the support graph to work here
    //// Find the minimum level of all support cubes. If it's >= k then we can
    //// push this cube straight to level min_lv+1 without consecution calls
    //int min_lv = support_graph->getMinSupportLevel(c);
    //if (min_lv >= level) {
    //  int next_lv = (min_lv == INT_MAX ? INT_MAX : min_lv + 1);
    //  logger.logorrheic() << "Pushing cube " << pc(c)
    //                      << " straight to level " << next_lv
    //                      << " due to supports" << std::endl;
    //  stats.free_pushes++;
    //  return next_lv;
    //}

    return QuipSolver::tryPropagate(lem, reduced);
  }

  void TrussSolver::constructSupportGraph(int level) {
    // There is no support graph at level 0
    assert(level > 0);
    assert(level == INT_MAX || level <= inductive_trace.getMaxFrame());

    logger.logorrheic() << "Constructing support graph for level "
                        << (level == INT_MAX ? "infinity" : std::to_string(level))
                        << std::endl;

    const Frame & f_i = inductive_trace.getFrame(level);

    for(auto it = f_i.begin(); it != f_i.end(); ++it) {
      const Cube & cube = inductive_trace.getCube(*it);
      assert(getActiveLemma(cube).level == level);
      computeSupport(cube);
    }
  }

  /*
   * Build the support graph from scratch.
   */
  void TrussSolver::constructSupportGraph() {
    support_graph.reset(new SupportGraph(inductive_trace));

    bool trivial = renewSAT();
    assert(!trivial);

    for (int i = 1; i <= inductive_trace.getMaxFrame(); ++i) {
      constructSupportGraph(i);
    }
  }

  /*
   * Write support graph to dot file.
   */
  void TrussSolver::writeSupportGraph() const {
    if (options().sg_infdot_file != "") {
      support_graph->writeInfDot(options().sg_infdot_file, badCube());
    }

    if (options().sg_dot_file != "") {
      support_graph->writeDot(options().sg_dot_file, badCube());
    }
  }

  void TrussSolver::onBeginLevel(int k) {
    (void) k;
    sg_obligations.clear();
  }

  std::pair<Cube, int> TrussSolver::afterSyntacticCheck(ProofObligation & po) {
    // For Truss, first try to meet the obligation using the support graph.
    // Note: this procedure is more complicated than necessary to implement
    // Truss. It supports a lot of other options.
    if (isActiveLemma(po.cube))
    {
      const Cube & cube = po.cube;
      int support_lvl = getSupportLevel(cube);
      if(support_lvl >= options().min_sg_level) {
        bool acceptable_known = hasAcceptableSupport(cube);
        if (!acceptable_known) {
          support_graph->deleteSupport(cube);
          logger.logorrheic() << "Support set unnacceptable, trying to find new one for"
                              << pc(cube)
                              << std::endl;
          acceptable_known = computeAcceptableSupport(cube);
        }

        if (!acceptable_known && options().desperate_sg) {
          support_graph->deleteSupport(cube);
          logger.logorrheic() << "Support set unnacceptable, desperately trying to find new one for"
                              << pc(cube)
                              << std::endl;
          acceptable_known = computeAcceptableSupport(cube, options().min_sg_level);
        }

        if (acceptable_known) {
          // Enqueue the support, re-enqeue po, continue
          size_t enqueued = 0;
          auto support_range = support_graph->getInEdges(cube);
          int min_lvl = INT_MAX;
          for (auto it = support_range.first; it != support_range.second; ++it) {
            CubeID id = *it;
            const Lemma & in_lem = getActiveLemma(id);
            const Cube & in_cube = in_lem.getCube();
            int lvl = in_lem.level;
            min_lvl = std::min(min_lvl, in_lem.level);
            if (lvl < po.level - 1) {
              logger.logorrheic() << "Enqueuing " << pc(in_cube)
                                  << " from level " << lvl
                                  << " to level " << po.level - 1
                                  << std::endl;
              ProofObligation & new_po = newObligation(in_cube, po.level - 1, NULL);
              new_po.type = MAY_PROOF;
              new_po.from_sg = true;
              sg_obligations.push_back(&new_po);
              pushObligation(new_po);
              enqueued++;
            }
          }

          logger.logorrheic() << "Acceptable support set found with "
                              << support_graph->getInDegree(cube)
                              << " lemmas (" << enqueued << " enqueued)"
                              << std::endl;

          // There's no guarantee anything will be enqueued, but if nothing
          // is, it should mean the obligation will pass
          if (enqueued > 0) {
            pushObligation(po);
            return std::make_pair(Cube(), -1);
          } else {
            assert(min_lvl >= po.level - 1);
            int to_lvl = min_lvl;
            if (to_lvl < INT_MAX) {
              to_lvl++;
            }
            logger.logorrheic() << "Sending " << pc(cube)
                                << " straight to level " << to_lvl
                                << std::endl;
            return std::make_pair(cube, to_lvl);
          }
        } else {
          logger.logorrheic() << "Unable to find acceptable support set" << std::endl;
        }
      } else {
        logger.logorrheic() << "Not seeking support set due to level "
                            << "(supported at: " << support_lvl << ")"
                            << std::endl;
      }
    }

    if (po.from_sg) {
      po.sg_effort++;
      // Skip because of effort - If we're below min_sg_level, then we use a
      // different limit than we'd use for higher levels. This is because
      // the levels below min_sg_level can't possibly have a support set
      int support_lvl = getSupportLevel(po.cube);
      int limit = (support_lvl < options().min_sg_level) ?
                           options().sg_effort_limit_minlvl :
                           options().sg_effort_limit;

      if (po.sg_effort > limit) {
        logger.logorrheic() << "Cube " << pc(po.cube)
                            << " marked ugly due to effort (used: "
                            << po.sg_effort - 1
                            << " / " << limit << ")"
                            << std::endl;
        markUgly(po.cube);

        for (ProofObligation * sgo : sg_obligations) {
          sgo->failed = true;
        }
        sg_obligations.clear();

        return std::make_pair(Cube(), -1);
      }
    }

    return std::make_pair(Cube(), -1);
  }

  void TrussSolver::onDischarge(ProofObligation & po, const Cube & t, int g) {
    // po->cube is blocked by ~t
    if (po.type == MAY_PROOF) {
      stats.may_success++;
    } else {
      stats.must_success++;
    }

    if (g < INT_MAX && (g + 1) < getLevel()) {
      if (options().reenqueue) {
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
  }

  void TrussSolver::onEndSolve() {
    // Optionally construct and write a support graph at the end
    if (options().do_final_sg) {
      constructSupportGraph();
    }

    if (options().do_final_sg) {
      writeSupportGraph();
    }
  }

  /*
   * We need to clear the list of obligations added from the support graph,
   * otherwise they are still lingering and might be written to, causing
   * memory corruption.
   */
  void TrussSolver::onClearObligations()
  {
      sg_obligations.clear();
  }

  /*
   * (Re-) initializes the solvers.
   * Returns true if any of the solvers indicate the problem is trivial
   */
  bool TrussSolver::renewSAT() {
    bool result = QuipSolver::renewSAT();
    if (result) { return true; }
    return trussRenewSAT();
  }

  bool TrussSolver::trussRenewSAT() {
    if (support_checker->renewSAT()) {
      return true;
    }

    return false;
  }

  void TrussSolver::printStats() const {
    // TODO: don't spread stats across several classes
    QuipSolver::printStats();

    if (options().do_final_sg) {
      support_graph->computeStats(badCube(), false);
      support_graph->printStats(false);
      support_graph->computeStats(badCube(), true);
      support_graph->printStats(true);
    }
  }

  void TrussSolver::onAddKnownCube(const Lemma & lem, int lv) {
    (void) lv;
    if (lem.bad) {
      stats.bad_lemmas_relearned++;
    }
    unmarkUgly(lem.getCube());
  }

  void TrussSolver::onDeleteLemma(CubeID id) {
    support_graph->deleteCube(id);
  }


}

