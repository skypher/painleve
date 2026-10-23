import Painleve.Calc
import Painleve.Phi

namespace Painleve
open MeasureTheory Finset
open scoped Matrix
open scoped ContDiff

lemma iter_smooth_real (F : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (n : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv n F) U := by
  induction n with
  | zero => rw [iteratedDeriv_zero]; exact hF
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (by simp)

lemma iter_hasDerivAt_real (F : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (n : ℕ) (x : ℝ) (hx : x ∈ U) :
    HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n + 1) F x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv n F) x :=
    ((iter_smooth_real F hU hF n).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

lemma iteratedDeriv_ofReal_comm (F : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    ∀ x ∈ U, iteratedDeriv n (fun t => ((F t : ℝ) : ℂ)) x
      = ((iteratedDeriv n F x : ℝ) : ℂ) := by
  induction n with
  | zero => intro x _; simp [iteratedDeriv_zero]
  | succ n ih =>
    intro x hx
    have hev : iteratedDeriv n (fun t => ((F t : ℝ) : ℂ)) =ᶠ[nhds x]
        (fun u => ((iteratedDeriv n F u : ℝ) : ℂ)) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun u hu => ih u hu)
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact ((iter_hasDerivAt_real F hU hF n x hx).ofReal_comp).deriv

lemma iteratedDeriv_add_eq (f : ℝ → ℂ) (p q : ℕ) :
    iteratedDeriv (p + q) f = iteratedDeriv p (iteratedDeriv q f) := by
  simp only [iteratedDeriv_eq_iterate]
  rw [Function.iterate_add]
  rfl

lemma sum_range_eq_of_zero (k p : ℕ) (hp : p < k) (f : ℕ → ℝ)
    (hf : ∀ i, p < i → f i = 0) :
    ∑ i ∈ Finset.range k, f i = ∑ i ∈ Finset.range (p + 1), f i := by
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_range, not_lt] at hx hx'
    exact hf x (by omega)

lemma iteratedDeriv_sum_const (s : Finset ℕ) (c : ℕ → ℂ) (G : ℕ → ℝ → ℂ)
    (hG : ∀ j, ContDiff ℝ ∞ (G j)) (p : ℕ) :
    iteratedDeriv p (fun t => ∑ j ∈ s, c j * G j t)
      = fun t => ∑ j ∈ s, c j * iteratedDeriv p (G j) t := by
  induction p with
  | zero => funext t; simp [iteratedDeriv_zero]
  | succ p ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    apply HasDerivAt.deriv
    have hd : ∀ j ∈ s, HasDerivAt (fun t => c j * iteratedDeriv p (G j) t)
        (c j * iteratedDeriv (p + 1) (G j) t) t := by
      intro j _
      rw [iteratedDeriv_succ]
      exact (((hG j).differentiable_iteratedDeriv p
        (by exact_mod_cast WithTop.coe_lt_top _)) t).hasDerivAt.const_mul (c j)
    exact HasDerivAt.fun_sum hd

lemma Phi_real_scaling (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (j : ℕ) (t : ℝ) :
    Real.exp t ^ j * iteratedDeriv j (Phi α β y) (Real.exp t)
      = ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2)) *
        (Real.exp (-(α / 2 + 1 / 4) * t) * Bmom α β (y * Real.exp (-t / 2)) 0 j) := by
  have hw : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hS := Phi_scaling α β y hα hy j (Real.exp t) hw
  have e1 : Real.exp t ^ (-(α / 2 + 1 / 4)) = Real.exp (-(α / 2 + 1 / 4) * t) := by
    rw [← Real.exp_mul]; congr 1; ring
  have e2 : Real.exp t ^ (-(1 / 2 : ℝ)) = Real.exp (-t / 2) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [e1, e2] at hS
  exact hS

lemma Phi_cplx_scaling (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (j : ℕ) (t : ℝ) :
    ((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j (fun x : ℝ => ((Phi α β y x : ℝ) : ℂ))
        (Real.exp t)
      = (((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) : ℝ) : ℂ) *
        (((Real.exp (-(α / 2 + 1 / 4) * t) : ℝ) : ℂ) *
          ((Bmom α β (y * Real.exp (-t / 2)) 0 j : ℝ) : ℂ)) := by
  have hD := iteratedDeriv_ofReal_comm (Phi α β y) isOpen_Ioi (Phi_contDiffOn α β y hα hy) j
    (Real.exp t) (Real.exp_pos t)
  rw [hD]
  have hR := congrArg (fun x : ℝ => (x : ℂ)) (Phi_real_scaling α β y hα hy j t)
  push_cast at hR ⊢
  linear_combination hR

lemma Phi_cplx_smooth (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) :
    ContDiffOn ℝ ∞ (fun x : ℝ => ((Phi α β y x : ℝ) : ℂ)) (Set.Ioi 0) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (Phi_contDiffOn α β y hα hy)

lemma Bmom_cplx_contDiffOn (α β : ℝ) (hα : 0 ≤ α) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun u : ℝ => ((Bmom α β u 0 j : ℝ) : ℂ)) (Set.Ioi 0) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (Bmom_contDiffOn α β hα 0 j)

lemma Bmom_comp_contDiff (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (j : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => ((Bmom α β (y * Real.exp (-t / 2)) 0 j : ℝ) : ℂ)) := by
  have hf : ContDiff ℝ ∞ (fun t : ℝ => y * Real.exp (-t / 2)) :=
    contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => Bmom α β (y * Real.exp (-t / 2)) 0 j) :=
    (Bmom_contDiffOn α β hα 0 j).comp_contDiff hf (fun t => mul_pos hy (Real.exp_pos _))
  exact Complex.ofRealCLM.contDiff.comp h1

lemma exp_cplx_contDiff (γ : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => ((Real.exp (-γ * t) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma iteratedDeriv_compExp_eq (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (q : ℕ) :
    iteratedDeriv q (fun t : ℝ => ((Phi α β y (Real.exp t) : ℝ) : ℂ))
      = fun t => ∑ j ∈ Finset.range (q + 1),
          (((stirS q j : ℝ) * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2)) : ℝ) : ℂ) *
            (((Real.exp (-(α / 2 + 1 / 4) * t) : ℝ) : ℂ) *
              ((Bmom α β (y * Real.exp (-t / 2)) 0 j : ℝ) : ℂ)) := by
  funext t
  have hΦ : iteratedDeriv q (fun t : ℝ => ((Phi α β y (Real.exp t) : ℝ) : ℂ)) t
      = ∑ j ∈ Finset.range (q + 1), (stirS q j : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ j *
          iteratedDeriv j (fun x : ℝ => ((Phi α β y x : ℝ) : ℂ)) (Real.exp t) :=
    iteratedDeriv_comp_exp (fun x : ℝ => ((Phi α β y x : ℝ) : ℂ)) (Phi_cplx_smooth α β y hα hy) q t
  rw [hΦ]
  apply Finset.sum_congr rfl
  intro j _
  have hC := Phi_cplx_scaling α β y hα hy j t
  push_cast at hC ⊢
  linear_combination (stirS q j : ℂ) * hC

lemma iteratedDeriv_Gj_zero (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (j p : ℕ) :
    iteratedDeriv p (fun t : ℝ => ((Real.exp (-(α / 2 + 1 / 4) * t) : ℝ) : ℂ) *
        ((Bmom α β (y * Real.exp (-t / 2)) 0 j : ℝ) : ℂ)) 0
      = ∑ i ∈ Finset.range (p + 1), ((kappa (α / 2 + 1 / 4) p i : ℝ) : ℂ) * (y : ℂ) ^ i *
          (((-1 : ℝ) ^ i * Bmom α β y i j : ℝ) : ℂ) := by
  have hs := iteratedDeriv_scaling (fun u : ℝ => ((Bmom α β u 0 j : ℝ) : ℂ))
    (Bmom_cplx_contDiffOn α β hα j) (α / 2 + 1 / 4) y hy p 0
  beta_reduce at hs
  rw [hs]
  have hv : ∀ i, iteratedDeriv i (fun u : ℝ => ((Bmom α β u 0 j : ℝ) : ℂ)) y
      = (((-1 : ℝ) ^ i * Bmom α β y i j : ℝ) : ℂ) := by
    intro i
    rw [iteratedDeriv_ofReal_comm (fun u => Bmom α β u 0 j) isOpen_Ioi
      (Bmom_contDiffOn α β hα 0 j) i y hy, iteratedDeriv_Bmom α β hα i j y hy]
  simp only [mul_zero, neg_zero, zero_div, Real.exp_zero, mul_one, Complex.ofReal_one, one_mul, hv]

lemma iteratedDeriv_compExp_entry (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (p q : ℕ) :
    iteratedDeriv p (iteratedDeriv q (fun t : ℝ => ((Phi α β y (Real.exp t) : ℝ) : ℂ))) 0
      = ∑ j ∈ Finset.range (q + 1),
          (((stirS q j : ℝ) * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2)) : ℝ) : ℂ) *
            ∑ i ∈ Finset.range (p + 1), ((kappa (α / 2 + 1 / 4) p i : ℝ) : ℂ) * (y : ℂ) ^ i *
              (((-1 : ℝ) ^ i * Bmom α β y i j : ℝ) : ℂ) := by
  have hsum := iteratedDeriv_sum_const (Finset.range (q + 1))
    (fun j => (((stirS q j : ℝ) * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2)) : ℝ) : ℂ))
    (fun j t => ((Real.exp (-(α / 2 + 1 / 4) * t) : ℝ) : ℂ) *
        ((Bmom α β (y * Real.exp (-t / 2)) 0 j : ℝ) : ℂ))
    (fun j => (exp_cplx_contDiff _).mul (Bmom_comp_contDiff α β y hα hy j)) p
  beta_reduce at hsum
  rw [iteratedDeriv_compExp_eq α β y hα hy q, hsum]
  simp only
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_Gj_zero α β y hα hy j p]

/-- The Hankel entry as a finite double sum (real form). -/
lemma Phi_hankel_entry (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (p q : ℕ) :
    iteratedDeriv (p + q) (fun t : ℝ => Phi α β y (Real.exp t)) 0
      = ∑ j ∈ Finset.range (q + 1),
          ((stirS q j : ℝ) * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2))) *
            ∑ i ∈ Finset.range (p + 1), kappa (α / 2 + 1 / 4) p i *
              (y ^ i * ((-1 : ℝ) ^ i * Bmom α β y i j)) := by
  have hFc : ContDiffOn ℝ ∞ (fun t : ℝ => Phi α β y (Real.exp t)) Set.univ :=
    ((Phi_contDiffOn α β y hα hy).comp_contDiff Real.contDiff_exp
      (fun t => Real.exp_pos t)).contDiffOn
  have hcoe := iteratedDeriv_ofReal_comm (fun t => Phi α β y (Real.exp t)) isOpen_univ hFc
    (p + q) 0 (Set.mem_univ _)
  have hC : ((iteratedDeriv (p + q) (fun t : ℝ => Phi α β y (Real.exp t)) 0 : ℝ) : ℂ)
      = ((∑ j ∈ Finset.range (q + 1),
          ((stirS q j : ℝ) * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2))) *
            ∑ i ∈ Finset.range (p + 1), kappa (α / 2 + 1 / 4) p i *
              (y ^ i * ((-1 : ℝ) ^ i * Bmom α β y i j)) : ℝ) : ℂ) := by
    rw [← hcoe, iteratedDeriv_add_eq, iteratedDeriv_compExp_entry α β y hα hy p q]
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  exact_mod_cast hC

lemma range_ext_sum (k p : ℕ) (hp : p < k) (f : ℕ → ℝ) (hf : ∀ i, p < i → f i = 0) :
    ∑ i ∈ Finset.range k, f i = ∑ i ∈ Finset.range (p + 1), f i :=
  sum_range_eq_of_zero k p hp f hf

/-- The Hankel matrix factors as `T · B · Λ · Sᵀ`. -/
lemma hankel_matrix_eq (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (k : ℕ) :
    (Matrix.of fun p q : Fin k =>
        iteratedDeriv ((p : ℕ) + (q : ℕ)) (fun t : ℝ => Phi α β y (Real.exp t)) 0)
      = (Matrix.of fun p i : Fin k => kappa (α / 2 + 1 / 4) (p : ℕ) (i : ℕ) * (-y) ^ (i : ℕ))
        * (Matrix.of fun i j : Fin k => Bmom α β y (i : ℕ) (j : ℕ))
        * Matrix.diagonal
            (fun j : Fin k => (-1 : ℝ) ^ (j : ℕ) * (ascPochhammer ℝ j).eval (β + 1 / 2))
        * (Matrix.of fun q j : Fin k => (stirS (q : ℕ) (j : ℕ) : ℝ))ᵀ := by
  ext p q
  have hp : (p : ℕ) < k := p.isLt
  have hq : (q : ℕ) < k := q.isLt
  rw [Matrix.of_apply, Phi_hankel_entry α β y hα hy p q, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have hin : ∀ j : Fin k,
      (∑ i : Fin k, kappa (α / 2 + 1 / 4) (p : ℕ) (i : ℕ) * (-y) ^ (i : ℕ) * Bmom α β y (i : ℕ) (j : ℕ))
        = ∑ i ∈ Finset.range k, kappa (α / 2 + 1 / 4) (p : ℕ) i * (-y) ^ i * Bmom α β y i (j : ℕ) :=
    fun j => Fin.sum_univ_eq_sum_range
      (fun i => kappa (α / 2 + 1 / 4) (p : ℕ) i * (-y) ^ i * Bmom α β y i (j : ℕ)) k
  simp only [hin]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (∑ i ∈ Finset.range k, kappa (α / 2 + 1 / 4) (p : ℕ) i * (-y) ^ i * Bmom α β y i j)
      * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2)) * (stirS (q : ℕ) j : ℝ)) k]
  have hpt : ∀ j : ℕ, ∑ i ∈ Finset.range k, kappa (α / 2 + 1 / 4) (p : ℕ) i * (-y) ^ i *
      Bmom α β y i j
      = ∑ i ∈ Finset.range ((p : ℕ) + 1), kappa (α / 2 + 1 / 4) (p : ℕ) i *
          (y ^ i * ((-1 : ℝ) ^ i * Bmom α β y i j)) := by
    intro j
    rw [range_ext_sum k (p : ℕ) hp (fun i => kappa (α / 2 + 1 / 4) (p : ℕ) i * (-y) ^ i *
      Bmom α β y i j) (fun i hi => by simp [kappa_eq_zero_of_lt _ hi])]
    apply Finset.sum_congr rfl
    intro i _
    rw [neg_pow]
    ring
  simp only [hpt]
  refine (range_ext_sum k (q : ℕ) hq _ ?_).symm.trans ?_
  · intro j hj
    simp [stirS_eq_zero_of_lt hj]
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem hankel_Phi_det (α β y : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hy : 0 < y) (k : ℕ) :
    (Matrix.of fun p q : Fin k =>
        iteratedDeriv ((p : ℕ) + q) (fun t => Phi α β y (Real.exp t)) 0).det =
      (-1) ^ (k * (k - 1) / 2) * (y / 2) ^ (k * (k - 1) / 2) *
        (∏ j : Fin k, (ascPochhammer ℝ j).eval (β + 1 / 2)) *
        (Matrix.of fun p q : Fin k => Bmom α β y p q).det := by
  rw [hankel_matrix_eq α β y hα hy k, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have hsum : ∑ i : Fin k, (i : ℕ) = k * (k - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id]
  have hT : (Matrix.of fun p i : Fin k =>
      kappa (α / 2 + 1 / 4) (p : ℕ) (i : ℕ) * (-y) ^ (i : ℕ)).det = (y / 2) ^ (k * (k - 1) / 2) := by
    have hL : (Matrix.of fun p i : Fin k =>
        kappa (α / 2 + 1 / 4) (p : ℕ) (i : ℕ) * (-y) ^ (i : ℕ)).IsLowerTriangular := by
      intro i j hij
      have h1 : (i : ℕ) < (j : ℕ) := Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 hij)
      simp [kappa_eq_zero_of_lt _ h1]
    rw [Matrix.det_of_isLowerTriangular _ hL]
    have hd : ∀ i : Fin k, (Matrix.of fun p i : Fin k =>
        kappa (α / 2 + 1 / 4) (p : ℕ) (i : ℕ) * (-y) ^ (i : ℕ)) i i = (y / 2) ^ (i : ℕ) := by
      intro i
      simp only [Matrix.of_apply]
      rw [kappa_self, ← mul_pow]
      congr 1
      ring
    rw [Finset.prod_congr rfl (fun i _ => hd i), Finset.prod_pow_eq_pow_sum, hsum]
  have hS : (Matrix.of fun q j : Fin k => (stirS (q : ℕ) (j : ℕ) : ℝ)).det = 1 := by
    have hL : (Matrix.of fun q j : Fin k => (stirS (q : ℕ) (j : ℕ) : ℝ)).IsLowerTriangular := by
      intro i j hij
      have h1 : (i : ℕ) < (j : ℕ) := Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 hij)
      simp [stirS_eq_zero_of_lt h1]
    rw [Matrix.det_of_isLowerTriangular _ hL]
    simp [stirS_self]
  have hD : (Matrix.diagonal fun j : Fin k =>
      (-1 : ℝ) ^ (j : ℕ) * (ascPochhammer ℝ j).eval (β + 1 / 2)).det
      = (-1) ^ (k * (k - 1) / 2) * ∏ j : Fin k, (ascPochhammer ℝ j).eval (β + 1 / 2) := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  rw [hT, hD, hS]
  ring

end Painleve
