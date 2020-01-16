#include "rts.h"
#include "smt-switch/smt.h"
#include "smt-switch/boolector_factory.h"

//

using namespace smt;
using namespace cosa;

// Note: we will be changing the input/state interface soon
// I can update this example file when that occurs

int main()
{
  SmtSolver s = BoolectorSolverFactory::create();
  RelationalTransitionSystem rts(s);

  // Types e.g. sorts
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort bvsort4 = s->make_sort(BV, 4);
  Sort arrsort = s->make_sort(ARRAY, bvsort4, bvsort8);

  // IVAR
  Term data = rts.make_input("data", bvsort8);

  // VAR
  Term x = rts.make_state("x", bvsort4);
  Term y = rts.make_state("y_A", bvsort4);
  // skipping the real number c
  Term mem = rts.make_state("mem", arrsort);

  // other terms
  Term zero = s->make_term("0", bvsort4);
  Term one = s->make_term("1", bvsort4);
  // uses decimal interpretation by default
  // can set to binary
  Term three = s->make_term("0011", bvsort4, 2);

  // INIT
  rts.constrain_init(s->make_term(Equal, x, zero));
  rts.constrain_init(s->make_term(Equal, y, one));

  // TRANS
  // example of functional update
  // when lhs is next(var) and rhs is all current state variables and inputs
  rts.set_next(y, y);
  rts.set_next(mem, s->make_term(Store, mem, y, data));
  // in the more general case, it might not be functional
  rts.constrain_trans(s->make_term(Equal, rts.next(x),
                                   s->make_term(BVAdd, y, three)));

  // Create the property
  Term prop;
  prop = s->make_term(Equal,
                      s->make_term(Select, rts.next(mem), rts.next(x)),
                      data);

  std::cout << "++++++++++++++++++++++++++ PRINT SIMPLE SYSTEM ++++++++++++++++++++++++++" << std::endl;
  std::cout << "INPUTS" << std::endl;
  for (auto i : rts.inputs())
  {
    std::cout << "\t" << i << std::endl;
  }
  std::cout << "STATES" << std::endl;
  for (auto s : rts.states())
  {
    std::cout << "\t" << s << std::endl;
  }
  std::cout << "INIT " << rts.init() << std::endl;
  std::cout << "TRANS " << rts.trans() << std::endl;
  std::cout << "INVARSPEC " << prop << std::endl;
  return 0;
}
