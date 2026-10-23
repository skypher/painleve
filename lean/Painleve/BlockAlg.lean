import Painleve.Gram
import Painleve.Calc

open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

/-- Weighted planar moments (body as in lane D's `wmom`, renamed `wmomE`). -/
noncomputable def wmomE (a : ℝ) (r k l : ℕ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))

/-- `z^r · z̄^r = ‖z‖^{2r}` as complex numbers. -/
lemma cast_norm_pow_two_mul (z : ℂ) (r : ℕ) :
    ((‖z‖ ^ (2 * r) : ℝ) : ℂ) = z ^ r * conj z ^ r := by
  have h : ‖z‖ ^ (2 * r) = (‖z‖ ^ 2) ^ r := by ring
  rw [h, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem blockGram_apply (a : ℝ) (r k : ℕ) (hr : r < 4) (p q : Fin k) :
    blockGram a r k p q = (-1 : ℂ) ^ (r + (q : ℕ)) * wmomE a r p q := by
  unfold blockGram wmomE
  rw [pairing_X_pow]
  have h1 : (r + 4 * (q : ℕ)) % 4 = r := by omega
  have h2 : (r + 4 * (q : ℕ)) / 4 = q := by omega
  rw [h1, h2, pow_add]
  congr 1
  congr 1
  funext z
  unfold density
  rw [pow_add, pow_add, cast_norm_pow_two_mul z r]
  ring


/-- Scaling rows and columns of a matrix by diagonal factors. -/
lemma det_row_col_scale {k : ℕ} (u v : Fin k → ℂ) (W : Matrix (Fin k) (Fin k) ℂ) :
    (Matrix.of fun p q : Fin k => u p * W p q * v q).det =
      (∏ p, u p) * (∏ q, v q) * W.det := by
  have hfac : (Matrix.of fun p q : Fin k => u p * W p q * v q)
      = Matrix.of fun i j : Fin k => u i * (Matrix.of fun i j : Fin k => v j * W i j) i j := by
    ext i j
    simp only [Matrix.of_apply]
    ring
  rw [hfac, Matrix.det_mul_column, Matrix.det_mul_row]
  ring

/-- The Gauss-sum power identity for `∏_{p : Fin k} c^p`. -/
lemma prod_fin_pow_val {k : ℕ} (c : ℂ) :
    ∏ p : Fin k, c ^ (p : ℕ) = c ^ (k * (k - 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) k,
    Finset.sum_range_id]

theorem det_blockGram (a : ℝ) (r k : ℕ) (hr : r < 4) :
    (blockGram a r k).det =
      (-1 : ℂ) ^ (r * k) * 16 ^ (k * (k - 1) / 2) *
        (Matrix.of fun p q : Fin k => (I / 4) ^ ((p : ℕ) + q) * wmomE a r p q).det := by
  have hcI : (4 / I) * (I / 4) = (1 : ℂ) := by
    field_simp
  have hc2 : (4 / I) * (4 / I) = (-16 : ℂ) := by
    rw [show (4 / I) * (4 / I) = 16 / (I * I) by ring, Complex.I_mul_I]
    norm_num
  have hB : blockGram a r k = ((-1 : ℂ) ^ r) •
      (Matrix.of fun p q : Fin k =>
        (4 / I) ^ (p : ℕ) * (Matrix.of fun p q : Fin k => (I / 4) ^ ((p : ℕ) + q) * wmomE a r p q) p q *
          ((-1 : ℂ) ^ (q : ℕ) * (4 / I) ^ (q : ℕ))) := by
    ext p q
    rw [blockGram_apply a r k hr p q]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have key : (4 / I) ^ ((p : ℕ) + q) * (I / 4) ^ ((p : ℕ) + q) = 1 := by
      rw [← mul_pow, hcI, one_pow]
    have hsplit : (4 / I) ^ (p : ℕ) * (4 / I) ^ (q : ℕ) = (4 / I) ^ ((p : ℕ) + q) :=
      (pow_add _ _ _).symm
    rw [pow_add]
    linear_combination ((-1 : ℂ) ^ r * (-1 : ℂ) ^ (q : ℕ) * wmomE a r p q) * (-1 : ℂ) * key
      + ((-1 : ℂ) ^ r * (-1 : ℂ) ^ (q : ℕ) * wmomE a r p q * (I / 4) ^ ((p : ℕ) + q)) * (-1 : ℂ) * hsplit
  rw [hB, Matrix.det_smul, Fintype.card_fin, det_row_col_scale, Finset.prod_mul_distrib,
    prod_fin_pow_val, prod_fin_pow_val, ← pow_mul]
  have e1 : (4 / I) ^ (k * (k - 1) / 2) * (4 / I) ^ (k * (k - 1) / 2) = (-16 : ℂ) ^ (k * (k - 1) / 2) := by
    rw [← mul_pow, hc2]
  have e2 : (-16 : ℂ) ^ (k * (k - 1) / 2) = (-1) ^ (k * (k - 1) / 2) * 16 ^ (k * (k - 1) / 2) := by
    rw [show (-16 : ℂ) = (-1) * 16 by norm_num, mul_pow]
  have e3 : (-1 : ℂ) ^ (k * (k - 1) / 2) * (-1) ^ (k * (k - 1) / 2) = 1 := by
    rw [← mul_pow]
    norm_num
  have hS : (4 / I) ^ (k * (k - 1) / 2) * ((-1) ^ (k * (k - 1) / 2) * (4 / I) ^ (k * (k - 1) / 2))
      = (16 : ℂ) ^ (k * (k - 1) / 2) := by
    linear_combination (-1 : ℂ) ^ (k * (k - 1) / 2) * e1 + (-1 : ℂ) ^ (k * (k - 1) / 2) * e2
      + (16 : ℂ) ^ (k * (k - 1) / 2) * e3
  linear_combination ((-1 : ℂ) ^ (r * k) * (Matrix.of fun p q : Fin k => (I / 4) ^ ((p : ℕ) + q) *
    wmomE a r p q).det) * hS


theorem det_stirling_conj (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    (Matrix.of fun p q : Fin k =>
        ∑ i : Fin k, ∑ j : Fin k, (stirS p i : ℂ) * (stirS q j : ℂ) * M i j).det = M.det := by
  set S : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun p i : Fin k => (stirS p i : ℂ) with hS
  have hmat : (Matrix.of fun p q : Fin k =>
      ∑ i : Fin k, ∑ j : Fin k, (stirS p i : ℂ) * (stirS q j : ℂ) * M i j) = S * M * S.transpose := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hS, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hlow : S.IsLowerTriangular := by
    intro p i hpi
    have hlt : p < i := OrderDual.toDual_lt_toDual.mp hpi
    simp only [hS, Matrix.of_apply]
    rw [stirS_eq_zero_of_lt (Fin.lt_def.mp hlt)]
    simp
  have hdetS : S.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular S hlow]
    refine Finset.prod_eq_one fun p _ => ?_
    simp [hS, stirS_self]
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetS, one_mul, mul_one]

end Painleve
