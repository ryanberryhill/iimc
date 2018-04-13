#ifndef _UMC_ENGINE_
#define _UMC_ENGINE_

#include "UMC.h"
#include "InductiveTrace.h"
#include "Initiation.h"
#include "Consecution.h"
#include "Generalization.h"
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

#include <boost/core/demangle.hpp>
#include <queue>

namespace UMC {

  // A simple obligation pool - list-based so we can maintain pointers into it
  typedef std::list<ProofObligation> ObligationPool;

  typedef std::priority_queue<ProofObligation&,
                              std::vector< std::reference_wrapper<ProofObligation> >,
                              ProofObligationComparator > ObligationQueue;

  /*
   * A struct wrapping references to some global elements that are
   * owned by the UMCEngine and also the model itself.
   */
  struct EngineGlobalState {
    Model & model;
    UMCStats & stats;
    Logger & logger;
    const UMCOptions & opts;
    InductiveTrace & inductive_trace;
    InitiationChecker & initiation_checker;
    Expr::Manager::View & ev;

    EngineGlobalState(Model & model,
                      UMCStats & stats,
                      Logger & logger,
                      const UMCOptions & opts,
                      InductiveTrace & inductive_trace,
                      InitiationChecker & initiation_checker,
                      Expr::Manager::View & ev) :
      model(model),
      stats(stats),
      logger(logger),
      opts(opts),
      inductive_trace(inductive_trace),
      initiation_checker(initiation_checker),
      ev(ev)

    { }

  };

  /*
   * Abstract UMC engine that defines the interface with the UMC engines along
   * with a few useful and typical functions that are needed internally.
   */
  class UMCEngine {
    public:
      UMCEngine(Model & m, UMCOptions o);
      UMCEngine(Model & m) : UMCEngine(m, UMCOptions()) { }
      virtual ~UMCEngine() { ev->end_local(); };

      // Primary interface to the solver
      virtual ReturnValue solve();
      // Can be called between runs
      virtual void reset(UMCOptions * new_opts = NULL) final;
      virtual void prepare(UMCOptions * new_opts = NULL);
      virtual void cleanup();

      virtual void printStats() const;

    protected:
      template<class T>
      T * checker(const IDSet & init) const {
        return new T(gs, init, getNPI(), badVar());
      }

      template<class T>
      T * checker(const Cube & init) const {
        IDSet init_set(init.begin(), init.end());
        return checker<T>(init_set);
      }

      template<class T>
      T * checker() const {
        return checker<T>(trueInitCube());
      }

      template<class T>
      T * exclusionaryChecker(LemmaFilter filter) const {
        T * chk = checker<T>();
        chk->setFilter(filter);
        return chk;
      }

      template<class G, class C = ConsecutionChecker>
      G * generalizer(C & cons_checker) {
        return new G(gs, cons_checker);
      }

      ConsecutionChecker * checkerFromString(const std::string & type) const;
      Generalizer * generalizerFromString(const std::string & type, ConsecutionChecker & cons);

      // Hooks
      virtual void onRenew() { }
      virtual void onBeginLevel(int k)
      { (void) k; }

      virtual void onEndSolve() { }
      virtual void onProofFound(std::vector<Cube> & proof);
      // If this returns false, skip the attempt to propagate
      virtual bool beforeTryPropagate(const Lemma &) { return true; }
      // Return the level to which the lemma is pushed. If the lemma cannot
      // be pushed, just return its current level.
      virtual int tryPropagate(const Lemma & lem, Cube & reduced);
      // Called when adding a new cube at lv
      virtual void onAddNewCube(const Lemma & lem, int lv)
      { (void) lem; (void) lv; }
      // Called when addCube is called on an already-known cube. lv is the
      // new level the cube is being promoted to
      virtual void onAddKnownCube(const Lemma & lem, int lv)
      { (void) lem; (void) lv; }
      // Called when adding any cube at lv, one of the above two is also called
      virtual void onAddCube(const Lemma & lem, int lv)
      { (void) lem; (void) lv; }
      // Called in proveBounded before block. Should check for obligation
      // failure and counter-example discovery
      virtual std::pair<bool, bool> beforeBlock(ProofObligation & po);
      // Called during block after the syntactic check but before the
      // consecution check
      virtual std::pair<Cube, int> afterSyntacticCheck(ProofObligation & po)
      { (void) po; return std::make_pair(Cube(), -1); }
      // Called when an obligation is discharged. Can be used to e.g., handle
      // the re-enqueue operations
      virtual void onDischarge(ProofObligation & po, const Cube & t, int g);
      // Called when the obligation has a predecessor. Should enqueue an
      // obligation for the predecessor state
      virtual void onPredecessor(ProofObligation & po, const Cube & inputs, const Cube & pred);
      // Called when a lemma is deleted (e.g., through infinity reduction)
      virtual void onDeleteLemma(CubeID id)
      { (void) id; }
      virtual void lemmaPushed(const Lemma & lem, int level, const Cube & reduced);
      virtual std::string getName() const { return "UMCEngine"; }

      // Functions for accessing options
      const Model & model() const { return m; }
      const UMCOptions & options() const { return opts; }

      // Functions related to specific SAT queries
      virtual bool initiation(const Cube & cube) const;
      virtual bool consecution(const Cube & c, int k,
                               SAT::Assignment * asgn = NULL,
                               Cube * reduced = NULL) = 0;
      virtual bool checkInitial(const Cube & bad_cube) const = 0;
      virtual bool checkInf(const Cube & bad_cube) const = 0;
      virtual void lift(Cube & t,
                        const Cube & inputs,
                        const Cube & p_inputs,
                        const Cube & s) const = 0;

      // Core functionalities
      virtual int generalize(int lo, int hi, Cube & cube) = 0;
      virtual std::pair<Cube, int> syntacticBlock(const ProofObligation & po);
      virtual std::pair<Cube, int> block(ProofObligation & po,
                                         Cube * inputs = NULL,
                                         Cube * concrete_state = NULL);
      virtual ReturnValue checkTrivial();
      virtual ReturnValue prove();
      virtual ReturnValue proveBounded(int k);
      virtual void pushClauses();
      virtual void reduceFinf();
      virtual void reduceFrames();
      virtual bool proofFound();
      virtual ReturnValue buildCex(ProofObligation & obl);
      virtual void renew() { AutoTimer timer(stats.renew_time); onRenew(); }

      // Proof obligation queue
      virtual bool obligationQueueEmpty() const;
      virtual ProofObligation & popObligation();
      virtual void pushObligation(ProofObligation & po);
      virtual ProofObligation & newObligation(const Cube & c, int k, ProofObligation * parent = NULL);
      virtual ProofObligation & copyObligation(ProofObligation & orig);
      virtual int numObligations() const;
      virtual void clearObligations();

      // Inductive trace funcitonality
      virtual void addCubeByID(CubeID id, int lv) final { addCube(inductive_trace.getCube(id), lv); }
      virtual void addCube(const Cube & cube, int lv);
      virtual void deleteLemma(const CubeID id);
      virtual const Lemma & getLemma(const Cube & cube) const final;
      virtual const Lemma & getLemma(CubeID id) const final;
      virtual const Lemma & getActiveLemma(const Cube & cube) const final;
      virtual const Lemma & getActiveLemma(CubeID id) const final;
      virtual bool isKnownLemma(const Cube & cube) const final;
      virtual bool isKnownLemma(CubeID id) const final;
      virtual bool isActiveLemma(const Cube & cube) const final;
      virtual bool isActiveLemma(CubeID id) const final;
      virtual bool isDeletedLemma(const Cube & cube) const final;
      virtual bool isDeletedLemma(CubeID id) const final;

      void deleteSubsumedLemma(CubeID id);
      void deleteSubsumedLemma(const Lemma & lem);
      void deleteAllSubsumedBy(CubeID id);
      void deleteAllSubsumedBy(const Lemma & lem);

      // Logging and output-related functions
      PrintCubePair pc(const Cube & cube) const { return std::make_pair(&cube, ev.get()); }
      void logObligation(const ProofObligation & po) const;
      void logAddCube(const std::string & prefix, const Lemma & lem, std::ostream & stream) const;

      // Level-tracking functions
      int getLevel() const { return current_level; }
      void setLevel(int level) { assert(level >= 0); current_level = level; }
      void incrementLevel() { current_level++; }
      void updateReachabilityBound(int k);

      // Utilities for interacting with the SAT solver
      void initializeAsgn(SAT::Assignment & asgn) const;
      void getCubesFromAsgn(const SAT::Assignment & asgn,
                            Cube * cube = NULL,
                            Cube * input_cube = NULL,
                            Cube * p_input_cube = NULL,
                            Cube * p_state_vars = NULL) const;
      ID parseSATResult(SAT::AssignVal val, ID lit) const;

      // Functions to access the circuit information
      bool inCOI(ID id) const { return coi_latches.find(id) != coi_latches.end(); }
      bool isInput(ID id) const { return input_vars.find(id) != input_vars.end(); }
      bool isStateVar(ID id) const { return state_vars.find(id) != state_vars.end(); }
      const Cube & initCube() const { return init_cube; }
      const IDSet & trueInitCube() const { return initially; }
      const IDSet & stateVars() const { return state_vars; }
      const IDSet & inputVars() const { return input_vars; }
      ID var(ID lit) const { return varOfLit(*ev, lit); }
      void prime(Expr::IDVector & vec) const;
      ID getNPI() const;
      ID badVar() const { return ev->newVar("bad"); }
      Cube badCube() const;

      // Member variables that subclasses should have direct access to
      std::unique_ptr<Expr::Manager::View> ev;
      // These are mutable because they are not conceptually part of the state
      // of the solver. Printing a log message does not change the state of
      // the solver, nor does incrementing a statistic counter
      mutable UMCStats stats;
      mutable Logger logger;

    private:
      void initCircuitData();
      void setOptions(const UMCOptions & new_opts) { opts = new_opts; }

      Model & m;
      UMCOptions opts;
      int current_level;
      IDSet state_vars;
      IDSet input_vars;
      IDSet coi_latches;
      Cube init_cube;
      IDSet initially;

      ObligationQueue obligations;
      ObligationPool obligation_pool;

    protected:
      InductiveTrace inductive_trace;
      InitiationChecker initiation_checker;
      EngineGlobalState gs;
  };

  /*
   * One action template handles all of the different tactics that subclass
   * UMCEngine.
   */
  template<class Solver>
  class UMCSolverAction : public Model::Action {
  public:

    UMCSolverAction(Model & m) : Model::Action(m)
    {
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
      COIAttachment::Factory caf;
      requires(Key::COI, &caf);
      RchAttachment::Factory raf;
      requires(Key::RCH, &raf);
      ProofAttachment::Factory paf;
      requires(Key::PROOF, &paf);
      CNFAttachment::Factory cnfaf;
      requires(Key::CNF, &cnfaf);
    }

    virtual void exec() override;

  private:
    static ActionRegistrar action;
  };

  template<class Solver>
  void UMCSolverAction<Solver>::exec()
  {
    Options::Verbosity verbosity = model().verbosity();
    std::string name =  boost::core::demangle(typeid(Solver).name());
    if (verbosity > Options::Silent) {
      std::cout << "Starting model checking (" << name << ")" << std::endl;
    }

    ReturnValue rv;
    try {
      Solver solver(model(), options());
      rv = solver.solve();
    } catch (std::exception &e) {
      if (verbosity > Options::Silent) {
        std::cout << "Exception caught in "
                  << name << ": "
                  << e.what() << std::endl;
      }
      throw e;
    }

    if (rv.returnType != MC::Unknown) {
      if (verbosity > Options::Silent) {
        std::cout << "Conclusion found by "
                  << name
                  << std::endl;
      }
    }

    auto pat = model().template attachment<ProofAttachment>(Key::PROOF);
    if (rv.returnType == MC::Proof) {
      pat->setConclusion(0);
      pat->setProof(rv.proof);
    }
    else if (rv.returnType == MC::CEX) {
      pat->setConclusion(1);
      pat->setCex(rv.cex);
    }
    model().release(pat);
  }

}

#endif

