import Painleve.HankelD
import Painleve.HankelSign
import Painleve.GammaRep
import Painleve.BlockSign

/-!
# Signs of the Gram blocks for general `d` (Proposition 5.2 of `paper.tex`)

`sgn Δ_k^{(r)} = (-1)^{rk + k(k-1)/2}`: by `cor:hankel`, `Δ_k^{(r)}` is
`(-1)^{rk} d^{2·binom(k,2)}` times the Hankel determinant of `F_r`, and by
`prop:gamma`, `F_r(t) = π r! a^{-r-1} φ(t + log κ)` with `φ` the function of
`lem:hankel-signs` for the shapes `β_{r,j}` and `κ = d^{d-2} a^{-d}`.
-/

open Complex Polynomial MeasureTheory Finset
open scoped ComplexConjugate ContDiff

namespace Painleve

variable {d : ℕ}

lemma shapeIdx_ne_nil (hd : 2 ≤ d) (r : ℕ) : shapeIdx d r ≠ [] := by
  by_cases h0 : (0 : ℕ) = d - 1 - r
  · refine List.ne_nil_of_mem (a := 1) ?_
    simp only [shapeIdx, List.mem_filter, List.mem_range, decide_eq_true_eq]
    omega
  · refine List.ne_nil_of_mem (a := 0) ?_
    simp only [shapeIdx, List.mem_filter, List.mem_range, decide_eq_true_eq]
    omega

lemma shapesD_cons (hd : 2 ≤ d) (r : ℕ) : ∃ β βs, shapesD d r = β :: βs := by
  have hne : shapesD d r ≠ [] := by
    unfold shapesD; simpa using shapeIdx_ne_nil hd r
  obtain ⟨β, βs, h⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨β, βs, h⟩

/-- `F_r(t) = π r! a^{-r-1} φ(t + log κ)` (`prop:gamma`). -/
lemma eqSrcD_eq_phiL (hd : 2 ≤ d) (r : ℕ) (hr : r < d) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    eqSrcD d a r t = ((Real.pi * r.factorial / a ^ (r + 1) *
      phiL (shapesD d r) (t + Real.log ((d : ℝ) ^ (d - 2) / a ^ d)) : ℝ) : ℂ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκ : 0 < (d : ℝ) ^ (d - 2) / a ^ d := by positivity
  rw [eqSrcD_eq_srcW, srcW_gamma d r hd hr ha]
  congr 2
  unfold phiL
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  congr 1
  rw [Real.exp_add, Real.exp_add, Real.exp_log hκ, ← Real.exp_nat_mul,
    show ((2 : ℕ) : ℝ) * (t / 2) = t by push_cast; ring]
  ring

/-- **Proposition 5.2** (`prop:block-determinants`). -/
theorem blockGramD_sign (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (r k : ℕ) (hr : r < d) :
    ∃ c : ℝ, 0 < c ∧
      (blockGramD d a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ) := by
  have hd0 : 0 < d := by omega
  obtain ⟨β, βs, hcons⟩ := shapesD_cons hd r
  have hpos : ∀ b ∈ β :: βs, 0 < b := by rw [← hcons]; exact shapesD_pos d r hd0
  have hβ : 0 < β := hpos β (by simp)
  have hβs : ∀ b ∈ βs, 0 < b := fun b hb => hpos b (by simp [hb])
  set A : ℝ := Real.pi * r.factorial / a ^ (r + 1) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set L : ℝ := Real.log ((d : ℝ) ^ (d - 2) / a ^ d) with hL
  set G : ℝ → ℝ := fun t => phiL (β :: βs) (t + L) with hG
  have hGsm : ContDiff ℝ ∞ G := (smoothBdd_phiL (β :: βs) hpos).1.comp
    (contDiff_id.add contDiff_const)
  have h1 := det_blockGramD hd0 a r k hr
  have h2 := det_stirling_conj k
    (Matrix.of fun i j : Fin k => (I / d) ^ ((i : ℕ) + j) * wmomD d a r i j)
  have h3 : (Matrix.of fun p q : Fin k => ∑ i : Fin k, ∑ j : Fin k,
      (stirS p i : ℂ) * (stirS q j : ℂ) *
        (Matrix.of fun i j : Fin k => (I / d) ^ ((i : ℕ) + j) * wmomD d a r i j) i j)
      = Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q) (eqSrcD d a r) 0 := by
    ext p q
    simp only [Matrix.of_apply]
    rw [← plane_hankelD hd0 a ha r p q]
    have e := sum_fin_range (k := k) (p : ℕ) (q : ℕ) p.isLt q.isLt
      (fun i j => (stirS (p : ℕ) i : ℂ) * (stirS (q : ℕ) j : ℂ) *
        ((I / d) ^ (i + j) * wmomD d a r i j))
      (fun i j hi => by simp [stirS_eq_zero_of_lt hi])
      (fun i j hj => by simp [stirS_eq_zero_of_lt hj])
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl).trans (e.trans ?_)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hFfun : eqSrcD d a r = fun t => ((A * G t : ℝ) : ℂ) := by
    funext t
    rw [eqSrcD_eq_phiL hd r hr ha t, hcons]
  have h4 : (Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q) (eqSrcD d a r) 0)
      = Matrix.of fun p q : Fin k => ((A * iteratedDeriv ((p : ℕ) + q) (phiL (β :: βs)) L : ℝ) : ℂ) := by
    ext p q
    simp only [Matrix.of_apply]
    rw [hFfun, iter_ofReal_const_mul A G hGsm]
    congr 2
    rw [hG, iteratedDeriv_comp_add_const]
    simp
  have h5 := det_ofReal_mat (Matrix.of fun p q : Fin k =>
    A * iteratedDeriv ((p : ℕ) + q) (phiL (β :: βs)) L)
  have h6 := det_const_mul' A (Matrix.of fun p q : Fin k =>
    iteratedDeriv ((p : ℕ) + q) (phiL (β :: βs)) L)
  have hH := hankel_sign β βs hβ hβs L k
  set H := (Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q) (phiL (β :: βs)) L).det
  set C := k * (k - 1) / 2
  refine ⟨((d : ℝ) ^ 2) ^ C * A ^ k * ((-1 : ℝ) ^ C * H), by positivity, ?_⟩
  rw [h1, ← h2, h3, h4]
  simp only [Matrix.of_apply] at h5 h6
  rw [h5, h6]
  have hsqC : ((-1 : ℂ) ^ C) * ((-1 : ℂ) ^ C) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  rw [pow_add]
  linear_combination (-(-1 : ℂ) ^ (r * k) * ((d : ℂ) ^ 2) ^ C * (A : ℂ) ^ k * (H : ℂ)) * hsqC

end Painleve
