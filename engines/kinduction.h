#pragma once

#include "prover.h"

namespace cosa {

class KInduction : public Prover
{
 public:
  KInduction(const Property & p, smt::SmtSolver & solver);
  ~KInduction();

  typedef Prover super;

  void initialize() override;

  ProverResult check_until(int k) override;

 protected:
  bool base_step(int i);
  bool inductive_step(int i);

  smt::Term simple_path_constraint(int i, int j);
  bool check_simple_path_lazy(int i);

  smt::Term init0_;
  smt::Term false_;
  smt::Term simple_path_;

};  // class KInduction

}  // namespace cosa
