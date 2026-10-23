import Painleve.Statement

/-!
# Statement of Theorem 1.2 (uniqueness of the positive solution)

Frozen Lean statement of Theorem 1.2 of `paper.tex` (label `thm:unique`):
for every `a > 0` (so `ε = a⁻²` ranges over all positive reals), two
sequences of positive numbers satisfying the quartic recurrence
`eq:quartic-recurrence` (with `v_n = 0` for `n < 0`, encoded by `extZ`)
coincide. No initial values are prescribed.
-/

namespace Painleve

/-- **Theorem 1.2** (`thm:unique`). -/
def Stmt_unique : Prop :=
  ∀ a : ℝ, 0 < a → ∀ v w : ℕ → ℝ,
    (∀ n, 0 < v n) → (∀ n, 0 < w n) → QuarticRec a v → QuarticRec a w → v = w

end Painleve
