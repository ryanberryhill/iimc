#include "UMC.h"
#include "Consecution.h"
#include "UMCEngine.h"
#include "Quip.h"
#include "Truss.h"
#include "BMC.h"
#include "Dispatch.h"
#include "IC3.h"
#include "IIC.h"


#include <boost/functional/hash.hpp>
#include <algorithm>

namespace std {

  /* Hash function for IDVectors (i.e., clauses or cubes) */
  std::size_t hash<Expr::IDVector>::operator()(const Expr::IDVector& c) const
  {
    using boost::hash_range;

    std::size_t seed = 0;

    hash_range(seed, c.begin(), c.end());

    return seed;
  }
}

/*
 * Stream operator for PrintCubePairs. This allows logging of cubes without
 * wrapping all log output if an if(verbosity > ...) and without the expense
 * of unconditionally generating strings for any cubes or clauses we want to
 * log.
 */
std::ostream& operator<<(std::ostream& os, UMC::PrintCubePair cube_ev)
{
  if (!os.good()) {
    return os;
  }

  Expr::Manager::View * ev;
  // Could be a clause too
  const UMC::Cube * cube;
  std::tie(cube, ev) = cube_ev;
  assert(cube);
  assert(ev);

  for (auto it = cube->begin(); it != cube->end(); ++it) {
    std::string strid = Expr::stringOf(*ev, *it);
    os << " " << strid;
  }

  return os;
}


namespace UMC {
  Logger null_log;

  void UMCAction::exec() {
    const unsigned hw_threads = std::thread::hardware_concurrency();
    const unsigned min_threads = model().options()["min_threads"].as<unsigned long>();
    const unsigned thread_limit = model().options()["thread_limit"].as<unsigned long>();
    // Upper bound is the lower of the user-provided limit and the hardware
    int num_threads = std::min(thread_limit, hw_threads);
    // Ensure at least equal to the user-provided minimum
    num_threads = std::max(min_threads, (unsigned) num_threads);
    // Force into the range [1,4]
    num_threads = std::max(num_threads, 1);
    num_threads = std::min(num_threads, 4);
    assert(num_threads > 0);
    assert(num_threads <= 4);

    if (model().verbosity() > Options::Terse) {
      std::cout << "Launching " << num_threads << " threads" << std::endl;
    }

    // Only do this stuff in IC3 mode, otherwise defer to IICAction
    if (model().defaultMode() == Model::mIC3) {
      switch (num_threads) {
        case 4:
          model().pushFrontTactic(new IC3::IC3Action(model(), false, false, "glucose"));
        case 3:
          model().pushFrontTactic(new UMC::UMCSolverAction<UMC::QuipSolver>(model()));
        case 2:
          model().pushFrontTactic(new BMC::BMCAction(model()));
        case 1:
          model().pushFrontTactic(new UMC::UMCSolverAction<UMC::TrussSolver>(model()));
          break;
        default:
          assert(false);
      }
      model().pushFrontTactic(new Dispatch::Fork(model()));
    } else {
      model().pushFrontTactic(new IIC::IICAction(model()));
    }
  }

  /*
   * Return true if a subsumes b, i.e. b is a subset of a.
   * Cubes are assumed to be sorted.
   */
  bool subsumes(const Cube & a, const Cube & b)
  {
#ifdef DEBUG
    assert(std::is_sorted(a.begin(), a.end()));
    assert(std::is_sorted(b.begin(), b.end()));
#endif
    size_t i = 0, j = 0;
    for (; j < b.size(); j++) {
      while (i < a.size() && a[i] != b[j]) {
        i++;
      }
      if (i == a.size()) { return false; }
    }
    return true;
  }

  bool cubeContains(const Cube & negCube, const std::set<ID> init)
  {
    for (auto it = negCube.begin(); it != negCube.end(); ++it) {
      if (init.find(*it) != init.end()) {
        return true;
      }
    }
    return false;
  }

  Cube negateCube(Expr::Manager::View & ev, const Cube & cube) {
    Cube negCube = cube;
    for (ID & c : negCube) {
      c = ev.apply(Expr::Not, c);
    }
    return negCube;
  }

  bool checkInitiation(Expr::Manager::View & ev, const Cube & cube, const std::set<ID> & init) {
    return cubeContains(negateCube(ev, cube), init);
  }

  /*
   * Returns the variable corresponding to the given literal. In other words,
   * removes any negation if present.
   */
  ID varOfLit(Expr::Manager::View & ev, ID lit) {
    Expr::Op op = ev.op(lit);
    ID var = ev.btrue();
    if (op == Expr::Var) {
      var = lit;
    } else {
      assert (op == Expr::Not);
      var = ev.apply(Expr::Not, lit);
    }
    assert(var != ev.btrue());
    return var;
  }

  void UMCStats::recordStat(std::vector<int> & stat, int x) {
    while ((int)stat.size() <= x) {
      stat.push_back(0);
    }
    stat[x]++;
  }

  std::string UMCStats::str(const std::vector<int> & stat) const {
    std::stringstream ss;
    for (unsigned i = 0; i < stat.size(); i++) {
      ss << " " << stat[i];
    }
    return ss.str();
  }

  void UMCStats::print() const
  {
    std::cout << "============================ Statistics ============================" << std::endl;
    std::cout << "Final level reached: " << level << std::endl;
    std::cout << "Number of initial state bits: " << init_state_bits << std::endl;
    std::cout << "Proof size: " << proof_size << std::endl;
    std::cout << "Number of consecution calls: " << consecution_calls << std::endl;
    std::cout << "Number of consecution calls from propagateClauses: " << cons_from_prop_cls << std::endl;
    std::cout << "Number of consecution calls from generalization: " << cons_from_gen << std::endl;
    std::cout << "Number of sat queries: " << sat_calls << std::endl;
    std::cout << "Number of cubes blocked by syntactic check: " << syntactic_block_success << std::endl;
    std::cout << "Number of cubes not blocked by syntactic check: " << syntactic_block_fail << std::endl;

    std::cout << "Average size of blocking cubes after generalization: " << (double)cube_size_total/cube_size_cnt << std::endl;
    std::cout << "Average size reduction of cubes during consecution: " << cube_reduction_total/cube_reduction_cnt << std::endl;

    std::cout << "Number of lemmas: " << total_lemmas << std::endl;
    std::cout << "Number of bad lemmas: " << bad_lemmas << std::endl;
    std::cout << "Number of ugly lemmas: " << ugly_lemmas << std::endl;
    std::cout << "Number of times lemmas were marked ugly: " << ugly_marked << std::endl;
    std::cout << "Number of times lemmas were unmarked ugly: " << ugly_unmarked << std::endl;
    std::cout << "Number of bad lemmas re-learned: " << bad_lemmas_relearned << std::endl;
    std::cout << "Number of infinity lemmas reduced: " << inf_cubes_reduced << std::endl;

    std::cout << "Number of support graph ``free pushes'': " << free_pushes << std::endl;

    std::cout << "Successful must proof obligations: " << must_success << std::endl;
    std::cout << "Successful may proof obligations: " << may_success << std::endl;
    std::cout << "Failed may proof obligations: " << may_fail << std::endl;
    std::cout << "Support set computations: " << support_calls << std::endl;
    std::cout << "Must proof obligation distribution by level:" << str(must_proof_dist) << std::endl;
    std::cout << "May proof obligation distribution by level:" << str(may_proof_dist) << std::endl;

    std::cout << "Time spent in model checking: " << solve_time << std::endl;
    std::cout << "Time spent processing must-proofs: " << must_time << std::endl;
    std::cout << "Time spent processing may-proofs: " << may_time << std::endl;
    std::cout << "Time spent computing support sets: " << support_time << std::endl;
    std::cout << "Time spent pushing: " << push_time << std::endl;
    std::cout << "Time spent SAT solving: " << sat_time << std::endl;
    std::cout << "Time spent in generalization: " << gen_time << std::endl;
    std::cout << "Time spent on reachable states: " << states_time << std::endl;
    std::cout << "Time spent on syntactic checks: " << syn_check_time << std::endl;
    std::cout << "Time spent reducing F_inf: " << reduce_inf_time << std::endl;
    std::cout << "Time spent reducing frames: " << reduce_frames_time << std::endl;
    std::cout << "Time spent initializing solvers: " << renew_time << std::endl;
    std::cout << "Time spent in lifting: " << lift_time << std::endl;
    std::cout << "Total reachable states discovered: " << total_states << std::endl;
    std::cout << "Unique reachable states (re-)discovered: " << unique_states << std::endl;
    std::cout << "Reachable state matches to proof obligations: " << state_matches << std::endl;

    std::cout << "Number of generalization approximation timeouts: " << gen_timeouts << std::endl;
    std::cout << "Number of lifting approximation timeouts: " << lift_timeouts << std::endl;
  }

}

