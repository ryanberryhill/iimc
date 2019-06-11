#ifndef _UMC_
#define _UMC_

#include "options.h"
#include "MC.h"
#include "ProofAttachment.h"
#include "ExprAttachment.h"
#include "CNFAttachment.h"
#include "RchAttachment.h"
#include "COI.h"
#include <iostream>
#include <set>
#include <list>

namespace std {

  template <>
  struct hash<Expr::IDVector>
  {
    std::size_t operator()(const Expr::IDVector& c) const;
  };

}

namespace UMC {
  typedef Expr::IDVector Cube;
  typedef Expr::IDVector Clause;
  typedef uint64_t CubeID;
  const CubeID CUBE_ID_NULL = 0;
  typedef std::set<CubeID> Frame;
  typedef std::set<ID> IDSet;

  // Defined in UMCEngine.h
  struct EngineGlobalState;

  /*
   * This action is analagous to the IICAction, but uses different
   * strategies, notably adding the UMCSolverActions
   */
  class UMCAction : public Model::Action {
  public:

    UMCAction(Model & m) : Model::Action(m)
    {
      ExprAttachment::Factory eaf;
      requires(Key::EXPR, &eaf);
      COIAttachment::Factory caf;
      requires(Key::COI, &caf);
      ProofAttachment::Factory paf;
      requires(Key::PROOF, &paf);
      CNFAttachment::Factory cnfaf;
      requires(Key::CNF, &cnfaf);
    }

    virtual void exec() override;

  private:
    static ActionRegistrar action;
  };

  struct ReturnValue {
    ReturnValue(MC::ReturnType returnType = MC::Unknown) : returnType(returnType) {}
    MC::ReturnType returnType;
    std::vector<Transition> cex;
    std::vector<Cube> proof;
  };

  /*
   * Useful free functions for general utility
   */
  bool subsumes(const Cube & a, const Cube & b);

  inline bool compareIDVectors(const Expr::IDVector & v1, const Expr::IDVector & v2) {
    auto it1 = v1.begin();
    auto it2 = v2.begin();
    for (; it1 != v1.end() && it2 != v2.end(); ++it1, ++it2) {
      if (*it1 < *it2) return true;
      if (*it1 > *it2) return false;
    }
    return (it1 == v1.end() && it2 != v2.end());
  }

  // Implements something like initiation. The problem is initiation
  // requires checking if the negation of a cube has any literals in
  // common with the initial state cube. But, negating a variable
  // requires access to the ExpressionView.
  // Initiation can be implemented as cubeContains(NOT(cube), initially)
  bool cubeContains(const Cube & negCube, const std::set<ID> init);
  Cube negateCube(Expr::Manager::View & ev, const Cube & cube);
  bool checkInitiation(Expr::Manager::View & ev, const Cube & cube, const std::set<ID> & init);
  ID varOfLit(Expr::Manager::View & ev, ID lit);

  struct CubeComp {
    bool operator() (const Cube & a, const Cube & b) {
      return compareIDVectors(a, b);
    }
  };

  typedef std::set<Cube, CubeComp> CubeSet;

  /*
   * Logging-related things
   *
   * The Logger class allows an easier logging interface. It exposes methods
   * for each level of verbosity that return a stream buffer. You can do things
   * like:
   *
   * log.verbose() << "Log message" << std::endl;
   *
   * and the message will only be written if the log level is verbose or
   * higher.
   *
   * PrintCubePair is an inelegant way of handling the expense of generating
   * strings from cubes or clauses. Often we need to log cubes or clauses.
   * It's somewhat expensive to iterate over their elements and generate a
   * string. By passing a PrintCubePair to the stream buffers of the Logger and
   * defining a operator<< that accepts a PrintCubePair, we can avoid the
   * expense of generating the strings when they won't be printed due to low
   * verbosity.
   */
  typedef std::pair<const std::vector<ID> *, Expr::Manager::View *> PrintCubePair;

  class Logger {

    std::ostream * log_logorrheic;
    std::ostream * log_verbose;
    std::ostream * log_informative;
    std::ostream * log_terse;
    std::ostream * log_silent;

    // This code is straight from StackOverflow
    // (http://stackoverflow.com/a/7818394)
    class null_out_buf : public std::streambuf {
      public:
        virtual std::streamsize xsputn (const char *, std::streamsize n) override {
            return n;
        }
        virtual int overflow (int) override {
            return EOF;
        }
    };

    class null_out_stream : public std::ostream {
      public:
        null_out_stream() : std::ostream (&buf) {}
      private:
        null_out_buf buf;
    };

    null_out_stream null_stream;

    public:

      Logger() :
          log_logorrheic(&null_stream),
          log_verbose(&null_stream),
          log_informative(&null_stream),
          log_terse(&null_stream),
          log_silent(&null_stream)
      { }

      Logger(Options::Verbosity verbosity) :
          log_logorrheic(&null_stream),
          log_verbose(&null_stream),
          log_informative(&null_stream),
          log_terse(&null_stream),
          log_silent(&null_stream)
      {
        setVerbosity(verbosity);
      }

      void setVerbosity(Options::Verbosity verbosity) {
        log_logorrheic = &null_stream;
        log_verbose = &null_stream;
        log_informative = &null_stream;
        log_terse = &null_stream;
        log_silent = &null_stream;
        switch(verbosity) {
          case Options::Logorrheic:
            log_logorrheic = &std::cout;
          case Options::Verbose:
            log_verbose = &std::cout;
          case Options::Informative:
            log_informative = &std::cout;
          case Options::Terse:
            log_terse = &std::cout;
          case Options::Silent:
            log_silent = &std::cout;
            break;
          default:
            log_silent = &std::cout;
            break;
        }
      }

      std::ostream & logorrheic(bool c = true)   { return c ? *log_logorrheic  : null_stream; }
      std::ostream & verbose(bool c = true)      { return c ? *log_verbose     : null_stream; }
      std::ostream & informative(bool c = true)  { return c ? *log_informative : null_stream; }
      std::ostream & terse(bool c = true)        { return c ? *log_terse       : null_stream; }
      std::ostream & silent(bool c = true)       { return c ? *log_silent      : null_stream; }
  };

  /* A null log object where all verbosity levels are disabled */
  extern Logger null_log;

  /*
   * Instrumentation-related classes.
   */

  /*
   * A manual stopwatch-style timer
   */
  class Timer {
    std::chrono::steady_clock::time_point begin_time, end_time;

    public:
      void begin() {
        begin_time = std::chrono::steady_clock::now();
      }

      void end() {
        end_time = std::chrono::steady_clock::now();
      }

      double elapsed() {
        std::chrono::duration<double> elapsed =
          std::chrono::duration_cast<std::chrono::duration<double> >
          (end_time - begin_time);
        return elapsed.count();
      }
  };

  /*
   * An automatic timer. Times the block in which it is instantiated, adds the
   * elapsed time to target
   */
  class AutoTimer {
    Timer timer;
    double & target;

    public:
      AutoTimer(double & target) : target(target)
      {
        timer.begin();
      }

      ~AutoTimer() {
        timer.end();
        target += timer.elapsed();
      }
  };

  enum ProofKind {MAY_PROOF, MUST_PROOF};

  struct ProofObligation {
    ProofObligation(const Cube & _cube,
                    int _level,
                    ProofObligation * _parent = NULL,
                    ProofKind _type = MUST_PROOF) :
                    cube(_cube),
                    level(_level),
                    type(_type),
                    parent(_parent),
                    failed(false),
                    from_sg(false),
                    sg_effort(0)
    {
      if (_parent) {
        depth = _parent->depth + 1;
      } else {
        depth = 0;
      }
    }

    ProofObligation(const ProofObligation & other)
    {
      cube      = other.cube;
      level     = other.level;
      type      = other.type;
      parent    = other.parent;
      depth     = other.depth;
      failed    = other.failed;
      cex_state = other.cex_state;
      inputs    = other.inputs;
      from_sg   = other.from_sg;
      sg_effort = other.sg_effort;
    }

    Cube cube;
    Cube cex_state;
    Cube inputs; //for reconstructing the cex trace
    int level;
    ProofKind type; //may or must
    ProofObligation * parent;
    int depth;
    bool failed;
    bool from_sg;
    int sg_effort;

    private:
      ProofObligation & operator=(const ProofObligation &) = delete;
  };

  class ProofObligationComparator {
  public:
    bool operator()(const ProofObligation & a, const ProofObligation & b) {
      if (a.type == b.type) {
        if (a.level == b.level) {
          return a.cube.size() > b.cube.size();
        }
        return a.level > b.level; //"largest" element for priority queue is lowest level
      } else {
        assert(a.type == MAY_PROOF || a.type == MUST_PROOF);
        assert(b.type == MAY_PROOF || b.type == MUST_PROOF);
        return a.type == MUST_PROOF;
      }
    }
  };

  class UMCStats {
  public:
    UMCStats() :
      level(0),
      resets(0),
      init_state_bits(0),
      sat_calls(0),
      consecution_calls(0),
      cons_from_gen(0),
      cons_from_prop_cls(0),
      syntactic_block_success(0),
      syntactic_block_fail(0),
      cube_size_total(0),
      cube_size_cnt(0),
      cube_reduction_total(0),
      cube_reduction_cnt(0),
      proof_size(0),
      free_pushes(0),
      bad_lemmas(0),
      total_lemmas(0),
      may_fail(0),
      may_success(0),
      must_success(0),
      may_time(0),
      must_time(0),
      support_time(0),
      solve_time(0),
      push_time(0),
      sat_time(0),
      gen_time(0),
      states_time(0),
      syn_check_time(0),
      reduce_inf_time(0),
      reduce_frames_time(0),
      renew_time(0),
      lift_time(0),
      ugly_lemmas(0),
      ugly_marked(0),
      ugly_unmarked(0),
      support_calls(0),
      bad_lemmas_relearned(0),
      inf_cubes_reduced(0),
      total_states(0),
      unique_states(0),
      state_matches(0),
      gen_timeouts(0),
      lift_timeouts(0)
    { }

    void print() const;

    int level;
    int resets;
    int init_state_bits;
    int sat_calls;
    int consecution_calls;
    int cons_from_gen;
    int cons_from_prop_cls;
    int syntactic_block_success;
    int syntactic_block_fail;

    int cube_size_total;
    int cube_size_cnt;
    double cube_reduction_total;
    int cube_reduction_cnt;
    int proof_size;
    int free_pushes;
    int bad_lemmas;
    unsigned total_lemmas;

    // Stats on proof obligations
    int may_fail;
    int may_success;
    int must_success;
    std::vector<int> may_proof_dist;
    std::vector<int> must_proof_dist;

    double may_time, must_time, support_time, solve_time, push_time;
    double sat_time, gen_time, states_time, syn_check_time;
    double reduce_inf_time, reduce_frames_time, renew_time;
    double lift_time;
    unsigned ugly_lemmas, ugly_marked, ugly_unmarked;
    unsigned support_calls;
    unsigned bad_lemmas_relearned;
    unsigned inf_cubes_reduced;

    // Reachable states
    unsigned total_states, unique_states, state_matches;

    unsigned gen_timeouts, lift_timeouts;

    void recordStat(std::vector<int> & stat,  int x);
    std::string str(const std::vector<int> & stat) const;
  };

  /*
   * A class representing all the data we know about a lemma.
   */
  class Lemma {
    public:
      Lemma () : bad(false),
                 ugly(false),
                 level(-1),
                 id(CUBE_ID_NULL)
      { }

      Lemma (Cube c,
             CubeID id,
             int level,
             bool bad = false) :
        bad(bad),
        ugly(false),
        level(level),
        cube(c),
        id(id)
      { }

      // Lemmas should be canonical, copying is forbidden
      Lemma(const Lemma & other) = delete;

      // Moving is allowed
      Lemma(Lemma && other) noexcept : bad(other.bad),
                                       ugly(other.ugly),
                                       level(other.level),
                                       cube(other.cube),
                                       id(other.id)
      {
        other.id = CUBE_ID_NULL;
        other.cube.clear();
        other.level = -1;
      }

      const Cube & getCube() const { return cube; }
      CubeID getID() const { return id; }

      bool bad;
      bool ugly;
      int level;
    private:
      Cube cube;
      CubeID id;
  };

  enum ExclusionType {
    ACTIVATION = 0,
    MULTI,
    LAZY,
    LAST_EXCLUSION_TYPE = LAZY
  };

  struct UMCOptions {
    std::string backend;
    std::string primary_cons;
    std::string support_cons;
    std::string gen;
    bool gen_random;
    std::string lift_style;
    std::string sg_infdot_file;
    std::string sg_dot_file;
    int max_reachable_states;
    bool print_stats;
    bool print_cex;
    bool lift;
    bool ugly_lemmas;
    bool do_final_sg;
    bool desperate_sg;
    bool reenqueue;
    bool reenqueue_both;
    bool excl_gen;
    bool excl_push;
    ExclusionType excl_type;
    bool reduce_inf;
    bool reduce_frames;
    bool subsumption_reduce;
    bool use_abbr;
    int min_sg_level;
    int sg_effort_limit;
    int sg_effort_limit_minlvl;
    int num_ctgs;
    int ctg_depth;
    int up_threshold;
    int gen_fails;
    int gen_budget;
    int lift_budget;
    int clear_queue_threshold;
    bool check_proof;

    UMCOptions() :  backend("glucose"),
                    primary_cons("multi"),
                    support_cons("activation"),
                    gen("down"),
                    gen_random(false),
                    lift_style("iter"),
                    sg_infdot_file(""),
                    sg_dot_file(""),
                    max_reachable_states(10000),
                    print_stats(false),
                    print_cex(false),
                    lift(true),
                    ugly_lemmas(true),
                    do_final_sg(false),
                    desperate_sg(false),
                    reenqueue(true),
                    reenqueue_both(true),
                    excl_gen(false),
                    excl_push(false),
                    excl_type(ACTIVATION),
                    reduce_inf(true),
                    reduce_frames(true),
                    subsumption_reduce(true),
                    use_abbr(true),
                    min_sg_level(1),
                    sg_effort_limit(1),
                    sg_effort_limit_minlvl(INT_MAX),
                    num_ctgs(3),
                    ctg_depth(1),
                    up_threshold(25),
                    gen_fails(-1),
                    gen_budget(-1),
                    lift_budget(-1),
                    clear_queue_threshold(INT_MAX),
                    check_proof(true)
    { }

    UMCOptions(
        const boost::program_options::variables_map & opts) : UMCOptions()
    {
      print_cex = opts.count("print_cex");

      // Use "" as the default in options.cpp, so that we only have to specify
      // the default once (in the intializer list here)
      std::string primary_cons_opt = opts["umc_primary_cons"].as<std::string>();
      std::string support_cons_opt = opts["truss_support_cons"].as<std::string>();
      std::string backend_opt = opts["umc_backend"].as<std::string>();
      std::string gen_opt = opts["umc_gen"].as<std::string>();
      std::string lift_opt = opts["umc_lift"].as<std::string>();

      if (!backend_opt.empty()) {
        backend = backend_opt;
      }

      if (!primary_cons_opt.empty()) {
        primary_cons = primary_cons_opt;
      }

      if (!support_cons_opt.empty()) {
        support_cons = support_cons_opt;
      }

      if (!gen_opt.empty()) {
        gen = gen_opt;
      }

      if (!lift_opt.empty()) {
        lift_style = lift_opt;
      }

      num_ctgs = opts["umc_num_ctgs"].as<int>();
      ctg_depth = opts["umc_ctg_depth"].as<int>();
      up_threshold = opts["umc_up_threshold"].as<int>();
      gen_random = opts["umc_gen_random"].as<bool>();
      gen_fails = opts["umc_gen_fails"].as<int>();
      gen_budget = opts["umc_gen_budget"].as<int>();
      lift_budget = opts["umc_lift_budget"].as<int>();

      print_stats = opts.count("umc_stats");

      max_reachable_states = opts["quip_max_reachable_states"].as<int>();
      lift = !opts.count("umc_xlift");

      do_final_sg = opts.count("truss_final_sg");
      desperate_sg = opts.count("truss_desperate_sg");
      min_sg_level = opts["truss_min_sg_level"].as<int>();
      reenqueue = opts.count("truss_reenq");
      reenqueue_both = opts.count("quip_xreenq_both");

      excl_gen        = opts.count("quip_excl_gen");
      excl_push       = opts.count("quip_excl_push");

      if (opts.count("quip_lazy_excl")) { excl_type = LAZY; }
      if (opts.count("quip_multi_excl")) { excl_type = MULTI; }

      reduce_inf = !opts.count("umc_xreduce_inf");
      reduce_frames = !opts.count("umc_xreduce_frames");
      subsumption_reduce = !opts.count("umc_xsubsumption");
      use_abbr = !opts.count("umc_xabbr");

      sg_effort_limit = opts["truss_effort_limit"].as<int>();
      sg_effort_limit_minlvl = opts["truss_effort_limit_minlvl"].as<int>();

      sg_infdot_file = opts["truss_infdot"].as<std::string>();
      sg_dot_file = opts["truss_dot"].as<std::string>();
      ugly_lemmas = !opts.count("truss_xugly");

      clear_queue_threshold = opts["quip_clear_queue"].as<int>();

      // Without ugly lemmas, the effort limits cause non-termination
      assert(sg_effort_limit == INT_MAX || ugly_lemmas);
      assert(sg_effort_limit_minlvl == INT_MAX || ugly_lemmas);
    }

  };

}

std::ostream& operator<<(std::ostream& os, UMC::PrintCubePair cube_ev);

#endif

