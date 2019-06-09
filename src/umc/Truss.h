#ifndef _TRUSS_
#define _TRUSS_


#include "UMC.h"
#include "Quip.h"

namespace UMC {

  class TrussSolver : public QuipSolver {
    enum ConsecutionType {
      CONSECUTION_NO_SG,
      CONSECUTION_SG,
      CONSECUTION_ACCEPTABLE_SG,
      LAST_CONSECUTION_TYPE = CONSECUTION_ACCEPTABLE_SG
    };
  public:
    TrussSolver(Model & m, UMCOptions o);
    TrussSolver(Model & m) : TrussSolver(m, UMCOptions()) { }
    ~TrussSolver() { }

    virtual void prepare(UMCOptions * new_opts = NULL) override;
    virtual void cleanup() override;

    virtual void printStats() const override;

  protected:
    virtual void onBeginLevel(int k) override;
    virtual void onEndSolve() override;
    virtual void onClearObligations() override;
    virtual int tryPropagate(const Lemma & lem, Cube & reduced) override;
    virtual void onAddKnownCube(const Lemma & lem, int lv) override;
    virtual void onDeleteLemma(CubeID id) override;
    virtual std::string getName() const override { return "Truss"; }

    virtual void onDischarge(ProofObligation & po, const Cube & t, int g) override;
    virtual std::pair<Cube, int> afterSyntacticCheck(ProofObligation & po) override;

    virtual bool renewSAT() override;

  private:
    void constructSupportGraph(int level);
    void writeSupportGraph() const;

    bool consecutionStandard(const Cube & c, int k, SAT::Assignment * asgn, Cube * reduced, ConsecutionType type);
    bool consecutionActivation(const Cube & c, int k, SAT::Assignment * asgn, Cube * reduced, ConsecutionType type);
    int getSupportLevel(const Cube & cube) const;
    bool computeAcceptableSupport(const Cube & cube, int lvl = -1);
    void computeSupport(const Cube & cube);
    void computeSupport(const Cube & cube, int lvl);
    void constructSupportGraph();
    void markUgly(const Cube & cube);
    void unmarkUgly(const Cube & cube);
    bool isAcceptable(const Cube & cube) const;
    bool isAcceptable(CubeID id) const;
    bool hasAcceptableSupport(const Cube & cube) const;
    bool hasBadSupport(const Cube & cube) const;

    void trussPrepare();
    void trussCleanup();
    bool trussRenewSAT();

    // Used in support set queries, or anywhere we need to exclude bad or
    // ugly lemmas
    std::unique_ptr<ConsecutionChecker> support_checker;
    std::unique_ptr<SupportGraph> support_graph;

    std::list<ProofObligation *> sg_obligations;
  };

  typedef UMCSolverAction<TrussSolver> TrussAction;

}

#endif

