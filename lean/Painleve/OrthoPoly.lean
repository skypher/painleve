import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Analysis.Complex.Basic

/-!
# Monic orthogonal polynomials for a sesquilinear Gram kernel

For a kernel `G : ℕ → ℕ → ℂ`, `sform G f g = Σ_{p,q} f_p conj(g_q) G p q` is the
sesquilinear form with Gram matrix `G` in the monomial basis. If the leading
minor `det [G p q]_{p,q<n}` is nonzero, there is a unique monic polynomial of
degree `n` orthogonal to `1, …, z^{n-1}`, and its square norm is the ratio of
consecutive leading minors (`eq:norm-delta-ratio`; only nonvanishing of the
minors is used, not positive definiteness).
-/

open Polynomial Matrix Finset
open scoped ComplexConjugate

namespace Painleve

/-- The sesquilinear form with Gram kernel `G`. -/
noncomputable def sform (G : ℕ → ℕ → ℂ) (f g : ℂ[X]) : ℂ :=
  f.sum fun p c => g.sum fun q d => c * conj d * G p q

/-- The leading `n × n` Gram matrix of `G`. -/
def gramM (G : ℕ → ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun p q => G p q

variable (G : ℕ → ℕ → ℂ)

theorem sform_X_pow_right (f : ℂ[X]) (j : ℕ) :
    sform G f (X ^ j) = f.sum fun p c => c * G p j := by
  unfold sform
  congr 1
  funext p c
  rw [X_pow_eq_monomial, sum_monomial_index]
  · simp
  · simp

theorem sform_X_pow_right_range (f : ℂ[X]) (j N : ℕ) (hN : f.natDegree < N) :
    sform G f (X ^ j) = ∑ i ∈ range N, f.coeff i * G i j := by
  rw [sform_X_pow_right, sum_over_range' f (fun n => by simp) N hN]

theorem sform_eq_sum_right (f g : ℂ[X]) :
    sform G f g = g.sum fun q d => conj d * sform G f (X ^ q) := by
  simp only [sform_X_pow_right]
  simp only [sform, Polynomial.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- Orthogonality of a polynomial of degree `< N` to `z^j`, written through the
Gram kernel. -/
theorem sform_X_pow_right_fin (f : ℂ[X]) (j n : ℕ) (hN : f.natDegree < n + 1) :
    sform G f (X ^ j) = (∑ i : Fin n, f.coeff i * G i j) + f.coeff n * G n j := by
  rw [sform_X_pow_right_range G f j (n + 1) hN, sum_range_succ, Finset.sum_range]

/-- A monic orthogonal polynomial is orthogonal to its own lower part, so its
square norm is its pairing with `z^n`. -/
theorem sform_self_eq (P : ℂ[X]) (n : ℕ) (hm : P.Monic) (hd : P.natDegree = n)
    (horth : ∀ j < n, sform G P (X ^ j) = 0) :
    sform G P P = sform G P (X ^ n) := by
  rw [sform_eq_sum_right, sum_over_range' P (fun n => by simp) (n + 1) (by omega),
    sum_range_succ, Finset.sum_eq_zero]
  · have : P.coeff n = 1 := by rw [← hd]; exact hm
    simp [this]
  · intro q hq
    rw [horth q (Finset.mem_range.mp hq), mul_zero]

/-- Determinant of a matrix whose last row vanishes off the diagonal. -/
theorem det_lastRow {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ j : Fin (n + 1), j ≠ Fin.last n → A (Fin.last n) j = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row A (Fin.last n), Fintype.sum_eq_single (Fin.last n)]
  · simp only [Fin.val_last, Fin.succAbove_last]
    rw [← two_mul, pow_mul]
    simp
  · intro j hj
    rw [h j hj]
    simp

/-- **Existence and uniqueness** of the monic orthogonal polynomial of degree `n`
when the leading minor of size `n` is nonzero. -/
theorem existsUnique_orthoPoly (n : ℕ) (hdet : (gramM G n).det ≠ 0) :
    ∃! P : ℂ[X], P.Monic ∧ P.natDegree = n ∧ ∀ j < n, sform G P (X ^ j) = 0 := by
  set A := gramM G n with hA
  have hAT : IsUnit Aᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  set b : Fin n → ℂ := fun j => G n j with hb
  set c : Fin n → ℂ := -(Aᵀ⁻¹ *ᵥ b) with hc
  have hsolve : Aᵀ *ᵥ c = -b := by
    rw [hc, mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hAT, one_mulVec]
  set Q : ℂ[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ) with hQ
  have hQdeg : degree Q < n := degree_sum_fin_lt c
  set P : ℂ[X] := X ^ n + Q with hP
  have hPm : P.Monic := monic_X_pow_add hQdeg
  have hPd : P.natDegree = n := by
    rw [hP, natDegree_add_eq_left_of_degree_lt] <;> simp [degree_X_pow, hQdeg]
  have hQcoeff : ∀ i : Fin n, Q.coeff i = c i := by
    intro i
    rw [hQ, finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · simp [coeff_C_mul, coeff_X_pow]
    · intro k _ hk
      simp only [coeff_C_mul, coeff_X_pow]
      rw [if_neg (fun h => hk (Fin.ext h.symm)), mul_zero]
    · simp
  have hPcoeff : ∀ i : Fin n, P.coeff i = c i := by
    intro i
    rw [hP, coeff_add, coeff_X_pow, if_neg (by omega), zero_add, hQcoeff]
  have hPn : P.coeff n = 1 := by rw [← hPd]; exact hPm
  refine ⟨P, ⟨hPm, hPd, fun j hj => ?_⟩, ?_⟩
  · rw [sform_X_pow_right_fin G P j n (by omega)]
    have := congrFun hsolve ⟨j, hj⟩
    simp only [mulVec, dotProduct, transpose_apply, hA, gramM, Pi.neg_apply, hb] at this
    simp only [hPcoeff, hPn, one_mul]
    rw [show (∑ i : Fin n, c i * G (i : ℕ) j) = ∑ i : Fin n, G (i : ℕ) j * c i by
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _, this]
    ring
  · rintro R ⟨hRm, hRd, hRorth⟩
    -- the difference has degree < n and is orthogonal to 1, …, z^{n-1}
    set v : Fin n → ℂ := fun i => R.coeff i - P.coeff i with hv
    have hRn : R.coeff n = 1 := by rw [← hRd]; exact hRm
    have hzero : Aᵀ *ᵥ v = 0 := by
      funext j
      have h1 := hRorth j j.2
      have h2 : sform G P (X ^ (j : ℕ)) = 0 := by
        rw [sform_X_pow_right_fin G P j n (by omega)]
        have := congrFun hsolve j
        simp only [mulVec, dotProduct, transpose_apply, hA, gramM, Pi.neg_apply, hb] at this
        simp only [hPcoeff, hPn, one_mul]
        rw [show (∑ i : Fin n, c i * G (i : ℕ) j) = ∑ i : Fin n, G (i : ℕ) j * c i by
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _, this]
        ring
      rw [sform_X_pow_right_fin G R j n (by omega)] at h1
      rw [sform_X_pow_right_fin G P j n (by omega)] at h2
      simp only [mulVec, dotProduct, transpose_apply, hA, gramM, hv, Pi.zero_apply]
      rw [hRn] at h1
      rw [hPn] at h2
      have : ∑ i : Fin n, G (i : ℕ) j * (R.coeff i - P.coeff i) =
          (∑ i : Fin n, R.coeff i * G i j) - ∑ i : Fin n, P.coeff i * G i j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      linear_combination h1 - h2
    have hv0 := eq_zero_of_mulVec_eq_zero (by rw [det_transpose]; exact hdet) hzero
    ext m
    rcases lt_trichotomy m n with hm | hm | hm
    · have := congrFun hv0 ⟨m, hm⟩
      simp only [hv, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · rw [hm, hRn, hPn]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

/-- **Norm formula**: `(P_n, P_n) · det G_n = det G_{n+1}`. -/
theorem sform_self_mul_det (n : ℕ) (P : ℂ[X]) (hm : P.Monic) (hd : P.natDegree = n)
    (horth : ∀ j < n, sform G P (X ^ j) = 0) :
    sform G P P * (gramM G n).det = (gramM G (n + 1)).det := by
  have hPn : P.coeff n = 1 := by rw [← hd]; exact hm
  set M := gramM G (n + 1) with hM
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i k => if (i : ℕ) < n then (if i = k then 1 else 0) else P.coeff k with hU
  have hUlow : U.IsLowerTriangular := by
    intro i k hik
    have hik' : i < k := hik
    simp only [hU, Matrix.of_apply]
    split_ifs with h1 h2
    · exact absurd h2 (ne_of_lt hik')
    · rfl
    · exact absurd (lt_of_lt_of_le hik' (Fin.le_last k)) (by
        intro h; have := Fin.lt_def.mp h; simp at this; omega)
  have hUdet : U.det = 1 := by
    rw [det_of_isLowerTriangular U hUlow]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [hU, Matrix.of_apply]
    split_ifs with h
    · rfl
    · have : (i : ℕ) = n := by omega
      rw [this, hPn]
  have hUM : (U * M).det = M.det := by rw [det_mul, hUdet, one_mul]
  have hrow : ∀ j : Fin (n + 1), (U * M) (Fin.last n) j = sform G P (X ^ (j : ℕ)) := by
    intro j
    rw [sform_X_pow_right_range G P j (n + 1) (by omega), ← Fin.sum_univ_eq_sum_range]
    simp only [mul_apply, hU, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, hM, gramM]
  have hlast : ∀ j : Fin (n + 1), j ≠ Fin.last n → (U * M) (Fin.last n) j = 0 := by
    intro j hj
    rw [hrow]
    exact horth j (Fin.val_lt_last hj)
  have hsub : (U * M).submatrix Fin.castSucc Fin.castSucc = gramM G n := by
    ext i j
    simp only [submatrix_apply, mul_apply, hU, Matrix.of_apply, Fin.val_castSucc, i.2, if_true,
      hM, gramM]
    rw [Fintype.sum_eq_single (Fin.castSucc i)]
    · simp
    · intro k hk
      rw [if_neg (Ne.symm hk), zero_mul]
  rw [← hUM, det_lastRow (U * M) hlast, hsub, hrow, Fin.val_last,
    sform_self_eq G P n hm hd horth]

end Painleve
