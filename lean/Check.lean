import Painleve
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Acceptance check: run `lake env lean Check.lean` after `lake build`. -/

open Lean Elab Command in
/-- Enforce the dependency policy, including dependencies of dependencies. -/
elab "assert_allowed_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do
    unless allowed.contains ax do
      throwError "unexpected axiom: {ax}"
  logInfo m!"{name}: allowed axioms {axioms}"

-- Regression: a dependency through a theorem must still be rejected.
namespace AxiomAuditRegression
axiom unwanted : False
theorem indirect : False := unwanted
/-- error: unexpected axiom: AxiomAuditRegression.unwanted -/
#guard_msgs in
assert_allowed_axioms indirect
-- Exercise the built-in admitted-proof axiom without an admitted theorem.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admittedDependency : False := sorryAx False true
/-- error: unexpected axiom: sorryAx -/
#guard_msgs in
assert_allowed_axioms admittedDependency
end AxiomAuditRegression

example : Painleve.Stmt_main := Painleve.main_theorem
example : Painleve.Stmt_unique := Painleve.unique_theorem
example : Painleve.Stmt_mainD := Painleve.main_theoremD

assert_allowed_axioms Painleve.main_theorem
assert_allowed_axioms Painleve.unique_theorem
assert_allowed_axioms Painleve.main_theoremD
