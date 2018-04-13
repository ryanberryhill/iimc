#ifndef _UMCIC3_
#define _UMCIC3_

#include "UMC.h"
#include "UMCEngine.h"
#include "ExprAttachment.h"
#include "CNFAttachment.h"
#include "COI.h"

namespace UMC {
  /*
   * A minimal example of how to customize the UMCEngine. The abstract
   * UMCEngine class almost implements IC3, but it doesn't specify how to do
   * any of the SAT queries. This class fills in those blanks.
   */
  class IC3Solver : public UMCEngine {
    public:
      IC3Solver(Model & m, UMCOptions o);
      IC3Solver(Model & m) : UMCEngine(m, UMCOptions()) { }
      virtual ~IC3Solver() { };

      virtual void prepare(UMCOptions * new_opts = NULL) override;
      virtual void cleanup() override;

    protected:
      virtual bool renewSAT();

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
      virtual bool proofFound() override;
      virtual void renew() override;
      virtual void pushClauses() override;
      virtual std::string getName() const override { return "IC3 (UMC)"; }

    private:
      void ic3Prepare();
      void ic3Cleanup();
      bool ic3RenewSAT();

      // Used in most consecution queries
      std::unique_ptr<ConsecutionChecker> cons_checker;
      // Used to check for initial state intersection
      std::unique_ptr<ConsecutionChecker> init_checker;
      // Used in lifting
      std::unique_ptr<UNSATCoreLifter> lifter;

      std::unique_ptr<Generalizer> gen;
  };

  typedef UMCSolverAction<IC3Solver> IC3Action;

}

#endif

