import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Derivatives of `exp(βv - c e^v)`

`d^n/dv^n exp(βv - c e^v) = exp(βv - c e^v) P_n(e^v)` with `P_0 = 1` and
`P_{n+1}(y) = (β - c y) P_n(y) + y P_n'(y)`; `P_n` has degree at most `n` and
`y^n`-coefficient `(-c)^n` (`lem:hankel-signs`). Consequently
`det[P_q(y_i)]_{i,q<k} = (-c)^{k(k-1)/2} V(y)`.
-/

open Polynomial Set Matrix

namespace Painleve

/-- The polynomials `P_n` for `exp(βv - c e^v)`. -/
noncomputable def derPoly (β c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C β - C c * X) * derPoly β c n + X * derivative (derPoly β c n)

/-- `exp(βv - c e^v)`. -/
noncomputable def expKerFn (β c v : ℝ) : ℝ := Real.exp (β * v - c * Real.exp v)

lemma contDiff_expKerFn (β c : ℝ) : ContDiff ℝ ⊤ (expKerFn β c) := by
  unfold expKerFn; fun_prop

lemma hasDerivAt_expKerFn_mul_poly (β c : ℝ) (P : ℝ[X]) (v : ℝ) :
    HasDerivAt (fun v => expKerFn β c v * P.eval (Real.exp v))
      (expKerFn β c v * ((C β - C c * X) * P + X * derivative P).eval (Real.exp v)) v := by
  have h1 : HasDerivAt (expKerFn β c) (expKerFn β c v * (β - c * Real.exp v)) v := by
    unfold expKerFn
    have := ((hasDerivAt_id v).const_mul β |>.sub ((Real.hasDerivAt_exp v).const_mul c)).exp
    simp only [id, mul_one] at this
    exact this
  have h2 : HasDerivAt (fun v => P.eval (Real.exp v))
      ((derivative P).eval (Real.exp v) * Real.exp v) v :=
    (P.hasDerivAt (Real.exp v)).comp v (Real.hasDerivAt_exp v)
  refine (h1.mul h2).congr_deriv ?_
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
  ring

theorem iteratedDeriv_expKerFn (β c : ℝ) (n : ℕ) :
    iteratedDeriv n (expKerFn β c) = fun v => expKerFn β c v * (derPoly β c n).eval (Real.exp v) := by
  induction n with
  | zero => funext v; simp [derPoly]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext v
    exact (hasDerivAt_expKerFn_mul_poly β c (derPoly β c n) v).deriv

lemma derPoly_natDegree_le (β c : ℝ) : ∀ n, (derPoly β c n).natDegree ≤ n
  | 0 => by simp [derPoly]
  | n + 1 => by
    have ih := derPoly_natDegree_le β c n
    unfold derPoly
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_mul_le).trans ?_
      have : (C β - C c * X : ℝ[X]).natDegree ≤ 1 := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · simp
        · exact (natDegree_C_mul_le _ _).trans (by simp)
      omega
    · refine (natDegree_mul_le).trans ?_
      have h1 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
      have h2 := (natDegree_derivative_le (derPoly β c n)).trans (Nat.sub_le_sub_right ih 1)
      omega

lemma derPoly_coeff_self (β c : ℝ) : ∀ n, (derPoly β c n).coeff n = (-c) ^ n
  | 0 => by simp [derPoly]
  | n + 1 => by
    have ih := derPoly_coeff_self β c n
    have hdeg := derPoly_natDegree_le β c n
    unfold derPoly
    rw [coeff_add, sub_mul, coeff_sub, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_mul,
      coeff_X_mul, coeff_derivative]
    have h0 : (derPoly β c n).coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0, ih]
    have h3 : (derPoly β c n).coeff (n + 1) = 0 := h0
    simp only [mul_zero, zero_sub, h3, zero_mul, add_zero]
    ring

/-- `det[P_q(y_i)]_{i,q<k}` for polynomials with `deg P_q ≤ q`. -/
theorem det_eval_polys {k : ℕ} (P : ℕ → ℝ[X]) (hdeg : ∀ q, (P q).natDegree ≤ q)
    (y : Fin k → ℝ) :
    (Matrix.of fun (i q : Fin k) => (P q).eval (y i)).det
      = (∏ q : Fin k, (P q).coeff q) * (Matrix.vandermonde y).det := by
  set U : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun (j q : Fin k) => (P q).coeff j with hU
  have hmat : (Matrix.of fun (i q : Fin k) => (P q).eval (y i)) = Matrix.vandermonde y * U := by
    ext i q
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply, hU]
    rw [eval_eq_sum_range' (n := k) (by have := hdeg q; have := q.isLt; omega)]
    rw [← Fin.sum_univ_eq_sum_range (fun j => (P q).coeff j * y i ^ j) k]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hup : U.BlockTriangular id := by
    intro j q hjq
    simp only [hU, Matrix.of_apply]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg q) hjq)
  rw [hmat, Matrix.det_mul, Matrix.det_of_upperTriangular hup, mul_comm]
  simp [hU]

lemma prod_neg_pow_fin (k : ℕ) (c : ℝ) :
    ∏ q : Fin k, (-c) ^ (q : ℕ) = (-c) ^ (k * (k - 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id]

/-- `det[P_q(y_i)] = (-c)^{k(k-1)/2} V(y)`. -/
theorem det_derPoly (β c : ℝ) {k : ℕ} (y : Fin k → ℝ) :
    (Matrix.of fun (i q : Fin k) => (derPoly β c q).eval (y i)).det
      = (-c) ^ (k * (k - 1) / 2) * (Matrix.vandermonde y).det := by
  rw [det_eval_polys (derPoly β c) (derPoly_natDegree_le β c) y]
  simp_rw [derPoly_coeff_self]
  rw [prod_neg_pow_fin]

/-- The Vandermonde determinant is positive at increasing points. -/
lemma det_vandermonde_pos {k : ℕ} (y : Fin k → ℝ) (hy : StrictMono y) :
    0 < (Matrix.vandermonde y).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
    sub_pos.mpr (hy (Finset.mem_Ioi.mp hj))

/-- A polynomial times `e^{-cy}` is bounded on `y ≥ 0` (`c > 0`). -/
lemma bdd_poly_mul_exp (P : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    ∃ C, ∀ y, 0 ≤ y → |P.eval y * Real.exp (-c * y)| ≤ C := by
  refine ⟨∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| * (j.factorial / c ^ j), fun y hy => ?_⟩
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_of_nonneg (pow_nonneg hy j), abs_of_pos (Real.exp_pos _)]
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le hy) j
  rw [div_le_iff₀ (by positivity)] at h
  have hE : Real.exp (-c * y) * Real.exp (c * y) = 1 := by rw [← Real.exp_add]; simp
  have hcj : 0 < c ^ j := pow_pos hc j
  rw [le_div_iff₀ hcj]
  calc y ^ j * Real.exp (-c * y) * c ^ j = (c * y) ^ j * Real.exp (-c * y) := by ring
    _ ≤ (Real.exp (c * y) * j.factorial) * Real.exp (-c * y) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = j.factorial := by linear_combination (j.factorial : ℝ) * hE

end Painleve
