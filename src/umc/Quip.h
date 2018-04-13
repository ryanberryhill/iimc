#ifndef _QUIP_
#define _QUIP_

#include "ExprAttachment.h"
#include "CNFAttachment.h"
#include "ProofAttachment.h"
#include "RchAttachment.h"
#include "COI.h"
#include "Model.h"
#include "SAT.h"
#include "MC.h"
#include "options.h"
#include "UMC.h"
#include "UMCEngine.h"
#include "InductiveTrace.h"
#include "Consecution.h"
#include "Generalization.h"
#include "SupportGraph.h"

#include <boost/program_options.hpp>
#include <list>

namespace UMC {

  struct ReachableState {
    ReachableState() {}
    ReachableState(Cube _state, Cube _inputs) :
      state(_state),
      pre(NULL),
      inputs(_inputs)
      {
#ifdef DEBUG
        assert(std::is_sorted(state.begin(), state.end()));
#endif
      }
    Cube state;
    ReachableState * pre; //predecessor state
    Cube inputs; //input assignment which led to this state
  };

  /*
   * A class that manages the reachable states discovered in Quip.  States are
   * stored in a list. They can never be deleted because they might be needed
   * to construct a counter-example trace. However, only the first N states in
   * the list are considered 'active.' Whenever a state intersects with an
   * obligation, it is promoted to the front of the list. The intersect
   * function only considers active states for performance reasons. This scheme
   * should keep the more-relevant states active.
   */
  class ReachableStateManager {
  public:

    ReachableStateManager(UMCStats & stats, size_t maxn_states) :
      stats(stats),
      maxn_states(maxn_states)
    { }

    ~ReachableStateManager() {
      clear();
    }

    void setMaxStates(size_t limit) { maxn_states = limit; }

    ReachableState * addState(const Cube & cube, const Cube & inputs);
    ReachableState * intersect(const Cube & cube);
    int getNumStates() const { return states.size(); }
    void clear() {
      for (ReachableState * r : states) {
        delete r;
      }
      states.clear();
    }

  private:
    UMCStats & stats;
    std::list<ReachableState*> states;
    size_t maxn_states;
  };

  class QuipSolver : public UMCEngine {
  public:
    QuipSolver(Model & m, UMCOptions o);
    QuipSolver(Model & m) : QuipSolver(m, UMCOptions()) { }
    virtual ~QuipSolver() { };

    virtual void prepare(UMCOptions * new_opts = NULL) override;
    virtual void cleanup() override;

  protected:
    // Specific SAT queries
    virtual bool consecution(const Cube & c, int k,
                             SAT::Assignment * asgn = NULL,
                             Cube * reduced = NULL) override;
    virtual bool checkInitial(const Cube & bad_cube) const override;
    virtual bool checkInf(const Cube & bad_cube) const override;
    virtual int generalize(int lo, int hi, Cube & cube) override;
    virtual void lift(Cube & t,
                      const Cube & inputs,
                      const Cube & p_inputs,
                      const Cube & s) const override;

    // Overridden hooks
    virtual void onRenew() override;
    virtual bool beforeTryPropagate(const Lemma & lem) override;
    virtual int tryPropagate(const Lemma & lem, Cube & reduced) override;
    virtual void onAddKnownCube(const Lemma & lem, int lv) override;
    virtual std::pair<bool, bool> beforeBlock(ProofObligation & po) override;
    virtual void onDischarge(ProofObligation & po, const Cube & t, int g) override;
    virtual void lemmaPushed(const Lemma & lem, int level, const Cube & reduced) override;
    virtual void reduceFrames() override;
    virtual bool renewSAT();
    virtual std::string getName() const override { return "Quip"; }

    // Handle reachable states in counter-examples
    virtual ReturnValue buildCex(ProofObligation & obl) override;

    ReachableState * extractReachable(ProofObligation & po, const Cube & r0);
    ReachableState * handleFailedMayProof(ProofObligation & po, const Cube & pred);

    void markBad(const Cube & cube);

  private:
    void quipPrepare();
    void quipCleanup();
    bool quipRenewSAT();
    ConsecutionChecker * constructExclChecker() const;

    // Used in most consecution queries
    std::unique_ptr<ConsecutionChecker> cons_checker;
    // Used to check for a proof and anywhere we want just F_inf and T
    std::unique_ptr<ConsecutionChecker> inf_checker;
    // Used to check for initial state intersection
    std::unique_ptr<ConsecutionChecker> init_checker;
    // Used for queries that need to exclude certain lemmas
    std::unique_ptr<ConsecutionChecker> excl_checker;
    // Used in lifting
    std::unique_ptr<UNSATCoreLifter> lifter;

    std::unique_ptr<Generalizer> gen;
    std::unique_ptr<Generalizer> excl_gen;

    ReachableStateManager rsman;
  };

  typedef UMCSolverAction<QuipSolver> QuipAction;

} // namespace UMC

#endif

