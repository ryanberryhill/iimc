#ifndef _GENERALIZATION_
#define _GENERALIZATION_

#include "UMC.h"
#include "Consecution.h"

namespace UMC {

  /*
   * A class that handles generalization. The main interface is through the
   * virtual generalize function. A range of levels is passed along with a
   * cube. The generalized cube is returned in the input cube, and the function
   * returns the level k where the generalized cube can be added to the trace.
   *
   * This class implements a lattice-based IC3-style generalization with
   * support for CTGs and both the up and down algorithms.
   */
  class Generalizer {
    private:
      bool join(Cube & cube, const SAT::Assignment & asgn, const std::set<ID> & keep) const;
      bool down(Cube & cube, int k, const std::set<ID> & keep, int limit = -1) const;
      void up(Cube & cube, int k, const std::set<ID> & keep) const;
      void prime_implicate(Cube & cube, int k, const std::set<ID> & keep) const;
      void prime_implicate(int k, const Cube & sup, Cube & s0) const;
      void mic(Cube & cube, int k, int limit = -1) const;
      void reduce(Cube & cube, const Cube & sup, const Cube & prev_cube, const Cube & crits) const;

    protected:
      InductiveTrace & inductive_trace;
      const Model & model;
      const UMCOptions & opts;
      Expr::Manager::View & ev;
      UMCStats & stats;
      ConsecutionChecker & cons_checker;
      InitiationChecker & initiation_checker;
      Logger & logger;

      PrintCubePair pc(const Cube & cube) const;

      virtual bool initiation(const Cube & cube) const;
      virtual void initiateCube(Cube & cube, const Cube & prev_cube) const;
      virtual bool consecution(Cube & c, int k, SAT::Assignment * asgn = NULL) const;
      virtual bool consecutionApprox(Cube & c, int k) const;
      virtual bool consecutionBudgeted(Cube & c, int k, int budget, SAT::Assignment * asgn = NULL) const;
      virtual int binsearch(Cube & cube, int lo, int hi) const;
      SAT::Assignment prepareCubeAssignment(const Cube & cube) const;
      Cube cubeFromAssignment(const SAT::Assignment & asgn) const;

    public:
      Generalizer(EngineGlobalState & gs,
                  ConsecutionChecker & cons);

      virtual ~Generalizer() { }

      virtual int generalize(int lo, int hi, Cube & c) const;
  };

  /*
   * This generalizer implements an iterative UNSAT-core based generalization
   * in the style of PDR
   */
  class IterativeGeneralizer : public Generalizer {
    public:
      IterativeGeneralizer(EngineGlobalState & gs,
                           ConsecutionChecker & cons) :
        Generalizer(gs, cons)
      { }

      virtual int generalize(int lo, int hi, Cube & c) const override;
  };
}

#endif

