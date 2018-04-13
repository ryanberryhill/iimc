#include <boost/program_options.hpp>
#include <string>

#include "Expr.h"
#include "ExprAttachment.h"
#include "ExprUtil.h"
#include "Model.h"
#include "Verbosity.h"
#include "options.h"
#include "COI.h"
#include "ProofAttachment.h"
#include "CNFAttachment.h"
#include "Quip.h"

ID var(Expr::Manager::View * ev, std::string name) {
  return ev->newVar(name);
}

class TestUMCAction : public Model::Action {
public:
  TestUMCAction(Model & m) : Model::Action(m)
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

  virtual void exec();


private:
  static ActionRegistrar action;
};

void TestUMCAction::exec() {
  UMC::QuipOptions opts;
  UMC::QuipSolver solver(model(), opts);
  UMC::ReturnValue rv = solver.solve();
  assert(rv.returnType == MC::CEX);
}

int main(void) {
  boost::program_options::variables_map opts;

  Model model(opts, "test");
  model.setVerbosity(Options::Verbose);
  model.setOptionValue("input-file", std::string("examples/quip_tests/unsafe/syncarb16.aig"));

  Model::Action * action = new TestUMCAction(model);
  action->make();
}
