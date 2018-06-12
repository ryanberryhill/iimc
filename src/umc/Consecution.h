#ifndef _CONSECUTION_
#define _CONSECUTION_

#include "UMC.h"
#include "InductiveTrace.h"
#include "Initiation.h"
#include <unordered_map>
#include <boost/core/demangle.hpp>

namespace UMC {

  typedef std::function<bool(const Lemma &)> LemmaFilter;
  extern LemmaFilter no_bad_no_ugly;

  struct ConsecutionOpts {
    int level;
    const Cube * cube;
    const Cube * unprimed_cube;
    SAT::Assignment * assignment;
    Cube * reduced;
    std::set<CubeID> * support_set;
    const Expr::IDVector * extra_assumps;
    LemmaFilter filter;
    int dec_budget;
    bool timed_out;

    ConsecutionOpts() : level(INT_MAX),
                        cube(NULL),
                        unprimed_cube(NULL),
                        assignment(NULL),
                        reduced(NULL),
                        support_set(NULL),
                        extra_assumps(NULL),
                        dec_budget(-1),
                        timed_out(false)
    { }
  };

  /*
   * ConsecutionChecker is an abstract class to manage solving consecution
   * queries.  It handles the SAT::Manager(s) and Views and can answer queries.
   * Subclasses can handle other variations on doConsecution queries. For
   * instance, UNSAT core lifting or support graph computations can be handled
   * by subclassing ConsecutionChecker or one of its concrete instantiations.
   */
  class ConsecutionChecker {
    private:
      // The transition relation stuff is private. For the moment I can't see
      // any need to override or use any of it differently in subclasses.
      ID badvar;
      ID property;
      std::vector<Clause> tr_clauses;
      LemmaFilter filter;
      bool stale;

      void constructTR(bool constraints);
      void cleanupTR();
      void initBad();
      std::vector<Clause> getConstraintClauses();

      // The following are not part of the state conceptually.
      // The SAT solvers and such are, but these are just intended
      // to cache activation literal mappings.
      mutable std::unordered_map<int, ID> index_to_act;
      mutable std::unordered_map<ID, int> act_to_index;

    protected:
      const UMCOptions & umc_opts;
      const InductiveTrace & inductive_trace;
      Expr::Manager::View & ev;
      Model & model;
      UMCStats & stats;
      Logger & logger;
      std::set<ID> initially;
      InitiationChecker & initiation_checker;

      PrintCubePair pc(const Cube & cube) const {
        return std::make_pair(&cube, &ev);
      }

      bool isFilteredOut(const Lemma & lem) const { return filter && !filter(lem); }
      virtual bool loadTR(SAT::Manager & manager) final;

      virtual void loadAllFrames();
      virtual void doLoadLemma(const Lemma & lem) = 0;
      virtual void loadLemma(const Lemma & lem) final;
      virtual ID activationLit(int index) const;
      virtual int inverseActivationLit(ID lit) const;
      virtual bool isActivationLit(ID lit) const;
      virtual ID toVar(ID lit) const;
      virtual ID getBad() final { return badvar; }
      virtual ID getBadPrime() final { return ev.prime(getBad()); }
      virtual ID getProperty() final { return property; }
      virtual ID getPropertyPrime() final { return Expr::primeFormula(ev, property); }
      virtual void reduceCube(const Cube & c, Cube & reduced, const Cube & crits) const;
      Expr::IDVector defaultAssumptions(ConsecutionOpts & opts) const;
      Expr::IDVector defaultCriticalAssumptions(ConsecutionOpts & opts) const;

      const UMCOptions & options() const { return umc_opts; }
      const std::string & backend() const { return options().backend; }
      virtual void setFilter(LemmaFilter f) { filter = f; }
      virtual bool initiation(const Cube & cube) const;

    public:
      /*
       * Construct the checker.
       *
       * bad: The ID of a special variable that appears in the inductive trace
       * and represents the "property lemma." There may (almost certainly will)
       * be a lemma in the trace ~bad. This should not be a variable that is
       * actually in the transition relation
       *
       * property: The ID of an expression that is equal to 1 when in a bad
       * state.
       *
       * init_state: A set representing a cube that represents the initial
       * states. Any cubes reduced during doConsecution will satisfy initiation
       * with respect to this cube.
       */
      ConsecutionChecker(const EngineGlobalState & gs,
                         std::set<ID> init_state,
                         ID property,
                         ID bad,
                         bool constraints = true);

      virtual ~ConsecutionChecker()
      {
        inductive_trace.deregisterConsecutionChecker(*this);
      }

      virtual bool renewSAT();
      virtual bool doRenewSAT() = 0;

      // The following are final because it would be quite surprising if
      // lemmaAdded(CubeId) did something different than just wrapping around
      // lemmaAdded(Lemma)
      virtual void lemmaDeleted(CubeID id) final;
      virtual void lemmaAdded(CubeID id) final;
      virtual void lemmaModified(CubeID id) final;
      virtual void lemmaPromoted(CubeID id) final;
      virtual void lemmaDemoted(CubeID id) final;

      virtual void lemmaDeleted(const Lemma & lem);
      virtual void lemmaAdded(const Lemma & lem);
      virtual void lemmaModified(const Lemma & lem);
      virtual void lemmaPromoted(const Lemma & lem);
      virtual void lemmaDemoted(const Lemma & lem);

      virtual bool consecution(const Cube & c, int k) final;
      virtual bool consecution(const Cube & c, int k, Cube & reduced) final;
      virtual bool consecution(ConsecutionOpts & opts) final;
      virtual bool doConsecution(ConsecutionOpts & opts) = 0;

      // They're the same filter, but to make it clear as to whether it's
      // a strong filter (applies at doConsecution-time) or a lazy filter
      // (applies at doRenewSAT/doLoadLemma -time) we have two separate functions
      virtual void setLazyFilter(LemmaFilter f) { setFilter(f); }
      virtual void setStrongFilter(LemmaFilter f)
      {
        (void) f;
        std::string name = boost::core::demangle(typeid(*this).name());
        std::string msg = name + " does not support strong filters";
        throw std::logic_error(msg);
      }
      virtual void clearFilter() { filter = nullptr; }

      void markStale() { stale = true; }
  };

  /*
   * LevelBasedConsecutionChecker manages doConsecution queries using the typical
   * strategy of per-level activation variables.
   */
  class LevelBasedConsecutionChecker : public ConsecutionChecker {
    protected:
      std::unique_ptr<SAT::Manager> sat_man;
      std::unique_ptr<SAT::Manager::View> sat_view;

      bool SATInitialized() { return bool(sat_man); }
      virtual void doLoadLemma(const Lemma & lem) override;

    public:
      LevelBasedConsecutionChecker(const EngineGlobalState & gs,
                                   std::set<ID> init_state,
                                   ID property,
                                   ID bad,
                                   bool constraints = true)
        : ConsecutionChecker(gs, init_state, property, bad, constraints)
      { }

      // It's unfortunately necessary (or at least reasonable) to have the
      // separate steps of construcing the checker and initializing/renewing
      // the SAT solver. This is because the SAT backends throw exceptions
      // when the SAT problem is trivial, and we don't want to deal with that
      // during the constructor.
      virtual bool doRenewSAT() override;

      virtual bool doConsecution(ConsecutionOpts & opts) override;
  };

  /*
   * A doConsecution checker than only includes absolute invariants (lemmas at
   * F_inf). Useful for UNSAT core lifting and extracting reachable states to
   * construct a counter-example.
   */
  class InfOnlyConsecutionChecker : public LevelBasedConsecutionChecker {
    protected:
      virtual void doLoadLemma(const Lemma & lem) override;
    public:
      InfOnlyConsecutionChecker(const EngineGlobalState & gs,
                                std::set<ID> init_state,
                                ID property,
                                ID bad,
                                bool constraints = true)
        : LevelBasedConsecutionChecker(gs, init_state, property, bad, constraints)
      { }
  };

  /*
   * A "doConsecution checker" with an additional function for UNSAT core
   * lifting and no actual support for doConsecution
   */
  class UNSATCoreLifter : public InfOnlyConsecutionChecker {
    protected:
      virtual bool oneLift(Cube & t,
                        const Cube & inputs,
                        const Cube & p_inputs,
                        const Cube & s,
                        bool exact = true) const;

      bool oneLiftApprox(Cube & t, const Cube & inputs, const Cube & p_inputs, const Cube & s) const
      { return oneLift(t, inputs, p_inputs, s, false); }

      virtual void iterLift(Cube & t,
                            const Cube & inputs,
                            const Cube & p_inputs,
                            const Cube & s) const;
      virtual void minLift(Cube & t,
                           const Cube & inputs,
                           const Cube & p_inputs,
                           const Cube & s) const;

    public:
      UNSATCoreLifter(const EngineGlobalState & gs,
                      std::set<ID> init_state,
                      ID property,
                      ID bad)
        : InfOnlyConsecutionChecker(gs, init_state, property, bad, false)
      { }

      virtual bool doConsecution(ConsecutionOpts & opts) override;
      virtual void lift(Cube & t,
                        const Cube & inputs,
                        const Cube & p_inputs,
                        const Cube & s) const;
  };

  /*
   * A checker that loads all lemmas and therefore represents checking
   * doConsecution from or intersection with initial states.
   */
  class InitialChecker : public LevelBasedConsecutionChecker {
    protected:
      virtual void doLoadLemma(const Lemma & lem) override;
    public:
      InitialChecker(const EngineGlobalState & gs,
                     std::set<ID> init_state,
                     ID property,
                     ID bad)
        : LevelBasedConsecutionChecker(gs, init_state, property, bad)
      { }
  };

  /*
   * A checker that loads absolute invariants only and therefore represents
   * checking against F_inf.
   */
  class InfChecker : public LevelBasedConsecutionChecker {
    protected:
      virtual void doLoadLemma(const Lemma & lem) override;
    public:
      InfChecker(const EngineGlobalState & gs,
                 std::set<ID> init_state,
                 ID property,
                 ID bad)
        : LevelBasedConsecutionChecker(gs, init_state, property, bad)
      { }
  };

  /*
   * A checker that uses a single SAT solver and unique activation literals
   * for each lemma. It is capable of handling support set computations
   */
  class ActivationBasedConsecutionChecker : public LevelBasedConsecutionChecker {
    protected:
      std::set<CubeID> loaded_lemmas, inf_loaded_lemmas;
      virtual void doLoadLemma(const Lemma & lem) override;
      std::set<CubeID> computeSupport(const Cube & crits) const;
    public:
      ActivationBasedConsecutionChecker(const EngineGlobalState & gs,
                                        std::set<ID> init_state,
                                        ID property,
                                        ID bad)
        : LevelBasedConsecutionChecker(gs, init_state, property, bad)
      { }

      virtual bool doConsecution(ConsecutionOpts & opts) override;
      virtual bool doRenewSAT() override;
      virtual void setStrongFilter(LemmaFilter f) override { setFilter(f); }

      virtual void lemmaDeleted(const Lemma & lem) override;
      virtual void lemmaDemoted(const Lemma & lem) override { (void) lem; }
  };

  /*
   * A checker with a SAT solver for each level. Warning: this checker doesn't
   * properly handle the underlying SAT backends throwing exceptions when the
   * problem is trivial (it just asserts that this doesn't happen).
   */
  class MultiSATConsecutionChecker : public ConsecutionChecker {
    private:
      typedef std::unique_ptr<SAT::Manager> SATManagerPtr;
      typedef std::unique_ptr<SAT::Manager::View> SATViewPtr;

      struct SATLevel {
        // The order of declaration is actually important here. The view will
        // be destroyed before the manager because it's declared after.  (This
        // is part of the language specification, so it's okay to depend on it)
        SATManagerPtr manager;
        SATViewPtr view;
        std::set<CubeID> loaded_lemmas;

        SATLevel(SAT::Manager * mgr, SAT::Manager::View * view) :
          manager(mgr), view(view)
        { }
      };

      std::unordered_map<int, SATLevel> levels;

      void setLoaded(int level, CubeID id);
      void initSAT(int level);

    protected:
      virtual bool isLoaded(int level, CubeID id) const final;
      virtual void addLemmaToManager(const Lemma & lem, SAT::Manager & manager);
      virtual bool safeToAdd(const Lemma & lem, int level) const;
      virtual void doLoadLemma(const Lemma & lem) override;
      SAT::Manager & getManager(int level);
      SAT::Manager::View & getView(int level);

    public:
      MultiSATConsecutionChecker(const EngineGlobalState & gs,
                                 std::set<ID> init_state,
                                 ID property,
                                 ID bad)
        : ConsecutionChecker(gs, init_state, property, bad)
      { }

      virtual bool doRenewSAT() override;
      virtual bool doConsecution(ConsecutionOpts & opts) override;
  };

  class ActivationMultiSATConsecutionChecker : public MultiSATConsecutionChecker {
    protected:
      virtual void addLemmaToManager(const Lemma & lem, SAT::Manager & manager) override;
      virtual std::set<CubeID> computeSupport(const Cube & crits) const;
    public:
      ActivationMultiSATConsecutionChecker(const EngineGlobalState & gs,
                                           std::set<ID> init_state,
                                           ID property,
                                           ID bad)
        : MultiSATConsecutionChecker(gs, init_state, property, bad)
      { }

      virtual bool doConsecution(ConsecutionOpts & opts) override;
      virtual void setStrongFilter(LemmaFilter f) override { setFilter(f); }
      virtual void lemmaDeleted(const Lemma & lem) override;
      virtual void lemmaDemoted(const Lemma & lem) override { (void) lem; }
  };
}

#endif

