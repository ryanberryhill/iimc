#ifndef _INITIATION_
#define _INITIATION_

#include "UMC.h"

namespace UMC {

  /*
   * An instance of this class defines what initiation means for the whole
   * UMC problem instance. Often initiation can be accomplished with a
   * syntactic check, but sometimes more complicated initial conditions
   * are needed (e.g., when constraints are present) necessitating SAT.
   */
  class InitiationChecker {
    public:
      InitiationChecker(const Model & m,
                        Expr::Manager::View & ev,
                        std::set<ID> initially = std::set<ID>());

      /*
       * Check for initiation of the given cube
       */
      bool initiation(const Cube & c) const;

      /*
       * Expand c to a larger cube that satisfies initation.
       */
      void initiateCube(Cube & c, const Cube & other) const;

      void setInit(const Cube & init);
      void setInit(const std::set<ID> & init) { initially = init;  }

    protected:
      const Model & m;
      Expr::Manager::View & ev;
      std::set<ID> initially;
  };
}

#endif
