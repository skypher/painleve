import Painleve.BlockSign
import Painleve.PlaneHankel

/-!
# Sign of every Gram block (Proposition 4.4 of `paper.tex`)

Combines the full-plane Hankel identity (`plane_hankel`) with the block-sign
argument (`det_blockGram_sign`).
-/

open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

theorem wmom_eq_wmomE : wmom = wmomE := rfl

theorem eqSrc_eq_wsrc (a : ℝ) (r : ℕ) :
    eqSrc a r = fun t : ℝ => wsrc r a (Real.exp (t / 2)) := by
  funext t
  unfold eqSrc wsrc
  congr 1
  funext z
  congr 2
  ring

/-- **Proposition 4.4.** Every Gram block determinant has the sign
`(-1)^{rk + k(k-1)/2}`. -/
theorem blockGram_sign (a : ℝ) (ha : 0 < a) (r k : ℕ) (hr : r < 4) :
    ∃ c : ℝ, 0 < c ∧
      (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ) := by
  refine det_blockGram_sign a ha r k hr fun p q => ?_
  have h := plane_hankel a ha r p q
  rw [wmom_eq_wmomE, eqSrc_eq_wsrc] at h
  exact h

end Painleve
