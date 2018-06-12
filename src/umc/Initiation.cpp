#include "Initiation.h"

namespace UMC {

  bool checkInitiation(Expr::Manager::View & ev, const Cube & cube, const std::set<ID> & init) {
    return cubeContains(negateCube(ev, cube), init);
  }

  InitiationChecker::InitiationChecker(const Model & m,
                                       Expr::Manager::View & ev,
                                       std::set<ID> initially)
        : m(m),
          ev(ev),
          initially(initially)
  { }

  void InitiationChecker::setInit(const Cube & init) {
    std::set<ID> init_set(init.begin(), init.end());
    setInit(init_set);
  }

  bool InitiationChecker::initiation(const Cube & c) const {
    return checkInitiation(ev, c, initially);
  }

  void InitiationChecker::initiateCube(Cube & c, const Cube & other) const {
    Cube super_cube = other;
    if (super_cube.empty()) {
      super_cube = Cube(initially.begin(), initially.end());
    }
#ifdef DEBUG
    assert(initiation(super_cube));
    assert(other.empty() || subsumes(other, c));
#endif

    for (ID lit : super_cube) {
      ID nlit = ev.apply(Expr::Not, lit);
      if (initially.count(nlit)) {
        c.push_back(lit);
        break;
      }
    }
  }
}

