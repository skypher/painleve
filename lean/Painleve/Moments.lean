import Painleve.Statement
import Painleve.Signs
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
open Complex MeasureTheory
open scoped ComplexConjugate
namespace Painleve

lemma norm_eta : ‖eta‖ = 1 := by
  unfold eta
  rw [Complex.norm_exp]
  simp

lemma conj_eta_pow_four : conj eta ^ 4 = -1 := by
  rw [← map_pow, eta_pow_four, map_neg, map_one]

lemma eta_mul_conj_eta : eta * conj eta = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_eta]
  norm_num

lemma I_pow_four_eq : I ^ 4 = 1 := by
  linear_combination (I ^ 2 - 1) * Complex.I_sq

lemma density_I_mul (a : ℝ) (z : ℂ) : density a (I * z) = density a z := by
  unfold density
  congr 1
  have h1 : ‖I * z‖ = ‖z‖ := by simp
  have h2 : (I * z) ^ 4 = z ^ 4 := by linear_combination z ^ 4 * I_pow_four_eq
  have h3 : conj (I * z) ^ 4 = conj z ^ 4 := by
    rw [map_mul, conj_I]
    linear_combination conj z ^ 4 * I_pow_four_eq
  rw [h1, h2, h3]

lemma density_eta_mul (a : ℝ) (z : ℂ) : density a (eta * z) = conj (density a z) := by
  unfold density
  rw [← Complex.exp_conj]
  congr 1
  have h1 : ‖eta * z‖ = ‖z‖ := by rw [norm_mul, norm_eta, one_mul]
  have h2 : (eta * z) ^ 4 = -z ^ 4 := by rw [mul_pow, eta_pow_four]; ring
  have h3 : conj (eta * z) ^ 4 = -conj z ^ 4 := by
    rw [map_mul, mul_pow, conj_eta_pow_four]; ring
  rw [h1, h2, h3]
  simp only [map_add, map_mul, map_neg, map_div₀, map_pow, conj_ofReal, conj_I, conj_conj,
    map_ofNat]
  ring

theorem norm_density (a : ℝ) (z : ℂ) : ‖density a z‖ = Real.exp (-a * ‖z‖ ^ 2) := by
  unfold density
  rw [Complex.norm_exp]
  congr 1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, z ^ 4 + conj z ^ 4 = (r : ℂ) := by
    refine ⟨(z ^ 4 + conj z ^ 4).re, ?_⟩
    have hc : conj (z ^ 4 + conj z ^ 4) = z ^ 4 + conj z ^ 4 := by
      simp only [map_add, map_pow, conj_conj]
      ring
    exact (Complex.conj_eq_iff_re.mp hc).symm
  rw [hr]
  have h4 : (I / 4) * (r : ℂ) = ((r / 4 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h4]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_im]
  ring

/-- Polynomial times Gaussian is dominated by a multiple of a smaller Gaussian. -/
lemma poly_gauss (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      t ^ n * Real.exp (-a * t ^ 2) ≤ C * Real.exp (-(a / 2) * t ^ 2) := by
  refine ⟨1 + (n.factorial : ℝ) * (2 / a) ^ n, fun t ht => ?_⟩
  have hE0 : 0 ≤ Real.exp (-(a / 2) * t ^ 2) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(a / 2) * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ a / 2) (sq_nonneg t)
    linarith
  have hsplit : Real.exp (-a * t ^ 2) = Real.exp (-(a / 2) * t ^ 2) * Real.exp (-(a / 2) * t ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hs : 0 ≤ a * t ^ 2 / 2 := by positivity
  have hEs : Real.exp (-(a / 2) * t ^ 2) = Real.exp (-(a * t ^ 2 / 2)) := by
    congr 1; ring
  have key : (a * t ^ 2 / 2) ^ n * Real.exp (-(a / 2) * t ^ 2) ≤ (n.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp _ hs n
    rw [div_le_iff₀ (by positivity)] at h
    have hm : Real.exp (-(a * t ^ 2 / 2)) * Real.exp (a * t ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    rw [hEs]
    calc (a * t ^ 2 / 2) ^ n * Real.exp (-(a * t ^ 2 / 2))
        ≤ (Real.exp (a * t ^ 2 / 2) * (n.factorial : ℝ)) * Real.exp (-(a * t ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = (n.factorial : ℝ) := by linear_combination (n.factorial : ℝ) * hm
  have hts : t ^ (2 * n) = (2 / a) ^ n * (a * t ^ 2 / 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hM : t ^ (2 * n) * Real.exp (-(a / 2) * t ^ 2)
      ≤ (2 / a) ^ n * (n.factorial : ℝ) := by
    rw [hts, mul_assoc]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  have hpow : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_total t 1 with h | h
    · have h1 : t ^ n ≤ 1 := pow_le_one₀ ht h
      have h2 : 0 ≤ t ^ (2 * n) := pow_nonneg ht _
      linarith
    · have h1 : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      have h2 : 0 ≤ (1 : ℝ) := zero_le_one
      linarith
  have hEE : Real.exp (-(a / 2) * t ^ 2) * Real.exp (-(a / 2) * t ^ 2)
      ≤ Real.exp (-(a / 2) * t ^ 2) :=
    mul_le_of_le_one_left hE0 hE1
  calc t ^ n * Real.exp (-a * t ^ 2)
      = t ^ n * (Real.exp (-(a / 2) * t ^ 2) * Real.exp (-(a / 2) * t ^ 2)) := by rw [hsplit]
    _ ≤ (1 + t ^ (2 * n)) * (Real.exp (-(a / 2) * t ^ 2) * Real.exp (-(a / 2) * t ^ 2)) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hE0 hE0)
    _ = Real.exp (-(a / 2) * t ^ 2) * Real.exp (-(a / 2) * t ^ 2)
          + (t ^ (2 * n) * Real.exp (-(a / 2) * t ^ 2)) * Real.exp (-(a / 2) * t ^ 2) := by ring
    _ ≤ Real.exp (-(a / 2) * t ^ 2) + ((2 / a) ^ n * (n.factorial : ℝ)) * Real.exp (-(a / 2) * t ^ 2) :=
        add_le_add hEE (mul_le_mul_of_nonneg_right hM hE0)
    _ = (1 + (n.factorial : ℝ) * (2 / a) ^ n) * Real.exp (-(a / 2) * t ^ 2) := by ring

lemma integrable_gauss (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℂ => Real.exp (-(a / 2) * ‖z‖ ^ 2)) := by
  have hb : 0 < ((a / 2 : ℝ) : ℂ).re := by simpa using half_pos ha
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Complex.norm_exp]
  congr 1
  rw [zero_mul, add_zero]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_im, ← Complex.ofReal_pow]
  ring

theorem integrable_moment (a : ℝ) (ha : 0 < a) (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * conj z ^ q * density a z) := by
  obtain ⟨C, hC⟩ := poly_gauss a ha (p + q)
  refine Integrable.mono' ((integrable_gauss a ha).const_mul C) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold density
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_density]
    rw [← pow_add]
    exact hC ‖z‖ (norm_nonneg z)

/-- Invariance of Lebesgue measure on `ℂ` under multiplication by a unit complex number. -/
lemma integral_rot_unit (u : ℂ) (hu : ‖u‖ = 1) (f : ℂ → ℂ) :
    ∫ z : ℂ, f (u * z) = ∫ z : ℂ, f z := by
  let w : Circle := ⟨u, mem_sphere_zero_iff_norm.2 hu⟩
  have hmp : MeasurePreserving (rotation w) volume volume := (rotation w).measurePreserving
  have hemb : MeasurableEmbedding (rotation w) := (rotation w).toHomeomorph.measurableEmbedding
  have := hmp.integral_comp hemb f
  simpa using this

theorem moment_eq_zero_of_mod_ne (a : ℝ) (p q : ℕ) (h : p % 4 ≠ q % 4) :
    ∫ z : ℂ, z ^ p * conj z ^ q * density a z = 0 := by
  have h1 : ∫ z : ℂ, (I * z) ^ p * conj (I * z) ^ q * density a (I * z)
      = ∫ z : ℂ, z ^ p * conj z ^ q * density a z :=
    integral_rot_unit I (by simp) (fun z => z ^ p * conj z ^ q * density a z)
  have h2 : ∀ z : ℂ, (I * z) ^ p * conj (I * z) ^ q * density a (I * z)
      = (I ^ p * (-I) ^ q) * (z ^ p * conj z ^ q * density a z) := by
    intro z
    rw [density_I_mul, map_mul, conj_I]
    simp only [mul_pow]
    ring
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  have hc : I ^ p * (-I) ^ q = I ^ (p + 3 * q) := by
    have h3 : -I = I ^ 3 := by linear_combination (-I) * Complex.I_sq
    rw [h3, ← pow_mul, pow_add]
  have hc1 : I ^ p * (-I) ^ q ≠ 1 := by
    intro h1'
    rw [hc, pow_eq_pow_mod _ I_pow_four_eq] at h1'
    rcases (show (p + 3 * q) % 4 = 0 ∨ (p + 3 * q) % 4 = 1 ∨ (p + 3 * q) % 4 = 2 ∨
        (p + 3 * q) % 4 = 3 by omega) with hr | hr | hr | hr
    · exact h (by omega)
    · rw [hr] at h1'
      norm_num [Complex.ext_iff, pow_succ] at h1'
    · rw [hr] at h1'
      norm_num [Complex.ext_iff, pow_succ] at h1'
    · rw [hr] at h1'
      norm_num [Complex.ext_iff, pow_succ] at h1'
  have hz : (1 - I ^ p * (-I) ^ q) * ∫ z : ℂ, z ^ p * conj z ^ q * density a z = 0 := by
    linear_combination (-1 : ℂ) * h1
  rcases mul_eq_zero.mp hz with h4 | h4
  · exact absurd (sub_eq_zero.mp h4).symm hc1
  · exact h4

theorem conj_moment (a : ℝ) (p q : ℕ) :
    conj (∫ z : ℂ, z ^ q * conj z ^ p * density a z) =
      conj eta ^ p * eta ^ q * ∫ z : ℂ, z ^ p * conj z ^ q * density a z := by
  rw [← integral_conj]
  have hL : ∫ z : ℂ, conj (z ^ q * conj z ^ p * density a z)
      = ∫ z : ℂ, z ^ p * conj z ^ q * density a (eta * z) := by
    congr 1
    funext z
    simp only [map_mul, map_pow, conj_conj, ← density_eta_mul]
    ring
  have hu : ‖conj eta‖ = 1 := by rw [Complex.norm_conj, norm_eta]
  have hrot : ∫ z : ℂ, (conj eta * z) ^ p * conj (conj eta * z) ^ q * density a (eta * (conj eta * z))
      = ∫ z : ℂ, z ^ p * conj z ^ q * density a (eta * z) :=
    integral_rot_unit (conj eta) hu (fun z => z ^ p * conj z ^ q * density a (eta * z))
  rw [hL, ← hrot, ← integral_const_mul]
  congr 1
  funext z
  have e : eta * (conj eta * z) = z := by rw [← mul_assoc, eta_mul_conj_eta, one_mul]
  rw [e, map_mul, conj_conj]
  simp only [mul_pow]
  ring

end Painleve
