import Painleve

/-! Acceptance check: run `lake env lean Check.lean` after `lake build`. -/

example : Painleve.Stmt_main := Painleve.main_theorem
example : Painleve.Stmt_unique := Painleve.unique_theorem
#print axioms Painleve.main_theorem
#print axioms Painleve.unique_theorem
