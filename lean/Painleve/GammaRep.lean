import Painleve.Polar
import Painleve.GammaLaw
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Gamma representation (Proposition 4.1 of `paper.tex`)

`𝒲_r(a; λ) = π r! a^{-r-1} E[exp(-λ² d^{d-2} a^{-d} S_r)]`, where `S_r` is a
product of independent Gamma variables with shapes `(r+1+j)/d`,
`j ∈ J_r = {0,…,d-1} \ {d-1-r}`.

Route: polar coordinates give `𝒲_r = ∫ R^{2r+1} e^{-aR²} K((2λ/d) R^d) dR`
(`srcW_polar`); in logarithmic coordinates this is an expectation over
`log U`, `U ~ Gamma(r+1)`. Gauss's multiplication formula identifies the law
of `d log U` with that of `d log d + log G + ∑_{j ∈ J_r} log G_j`, with `G`
exponential (`law_eq`), and the Gaussian integral
`∫ e^{-|w|²} e^{2iγ Re w} dA = π e^{-γ²}` integrates out `G` (`gauss_K`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate Real

namespace Painleve

/-! ### Logarithmic coordinates -/

/-- `∫_0^∞ R^{2r+1} e^{-aR²} K(c R^d) dR = ½ ∫ e^{(r+1)v - a e^v} K(c e^{dv/2}) dv`. -/
theorem radial_log (d r : ℕ) (a c : ℝ) :
    ∫ R in Ioi (0 : ℝ), ((R ^ (2 * r + 1) * Real.exp (-a * R ^ 2) : ℝ) : ℂ) * angK (c * R ^ d)
      = (1 / 2 : ℂ) * ∫ v : ℝ, ((Real.exp ((r + 1) * v - a * Real.exp v) : ℝ) : ℂ) *
          angK (c * Real.exp (d * v / 2)) := by
  rw [← integral_exp_smul_comp]
  set F : ℝ → ℂ := fun w => Real.exp w • (((Real.exp w ^ (2 * r + 1) *
      Real.exp (-a * Real.exp w ^ 2) : ℝ) : ℂ) * angK (c * Real.exp w ^ d)) with hF
  have hs := Measure.integral_comp_mul_left F (1 / 2 : ℝ)
  rw [show |(1 / 2 : ℝ)⁻¹| = 2 by norm_num] at hs
  have hpt : ∀ v : ℝ, ((Real.exp ((r + 1) * v - a * Real.exp v) : ℝ) : ℂ) *
      angK (c * Real.exp (d * v / 2)) = F (1 / 2 * v) := by
    intro v
    have e1 : Real.exp (1 / 2 * v) ^ (2 * r + 1) = Real.exp ((2 * r + 1 : ℕ) * (1 / 2 * v)) :=
      (Real.exp_nat_mul _ _).symm
    have e2 : Real.exp (1 / 2 * v) ^ 2 = Real.exp v := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : Real.exp (1 / 2 * v) ^ d = Real.exp (d * v / 2) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hr : Real.exp (1 / 2 * v) * (Real.exp ((2 * r + 1 : ℕ) * (1 / 2 * v)) *
        Real.exp (-a * Real.exp v)) = Real.exp ((r + 1) * v - a * Real.exp v) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
    simp only [hF]
    rw [e1, e2, e3, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hr]
  have h2 : ∫ v : ℝ, ((Real.exp ((r + 1) * v - a * Real.exp v) : ℝ) : ℂ) *
        angK (c * Real.exp (d * v / 2)) = 2 * ∫ w : ℝ, F w := by
    rw [integral_congr_ae (Eventually.of_forall hpt), hs, Complex.real_smul]
    push_cast; ring
  rw [h2]
  ring

/-! ### The Gaussian identity -/

/-- `𝒲_0(1; γ)` for `d = 1` is the Gaussian integral
`∫_ℂ e^{-|w|²} e^{2iγ Re w} dA = π e^{-γ²}`. -/
lemma srcW_gauss (γ : ℝ) : srcW 1 0 1 γ = (π : ℂ) * cexp (-(γ : ℂ) ^ 2) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp)
    (2 * γ * I) (1 : ℂ)
  have hfin : ((Module.finrank ℝ ℂ : ℕ) : ℂ) / 2 = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hfin, cpow_one, div_one] at h
  have hl : ∀ z : ℂ, ((‖z‖ ^ (2 * 0) : ℝ) : ℂ) *
      cexp (-((1 : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * γ / ((1 : ℕ) : ℂ)) * (z ^ 1 + conj z ^ 1))
      = cexp (-1 * (‖z‖ : ℂ) ^ 2 + 2 * γ * I * ((inner ℝ (1 : ℂ) z : ℝ) : ℂ)) := by
    intro z
    have hz : z + conj z = ((2 * z.re : ℝ) : ℂ) := by rw [Complex.add_conj]
    rw [Complex.inner, map_one, mul_one, pow_one, pow_one, hz]
    simp only [mul_zero, pow_zero, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  unfold srcW
  rw [integral_congr_ae (Eventually.of_forall hl), h]
  congr 1
  congr 1
  simp only [norm_one, Complex.ofReal_one, one_pow, mul_one]
  ring_nf
  rw [I_sq]
  ring

/-- **The exponential factor integrates out**: for `G ~ Exp(1)`,
`E[K(2γ G^{1/2})] = 2π e^{-γ²}`, in logarithmic coordinates. -/
theorem gauss_K (γ : ℝ) :
    ∫ v : ℝ, qLog 1 v • angK (2 * γ * Real.exp (v / 2))
      = 2 * (π : ℂ) * ((Real.exp (-γ ^ 2) : ℝ) : ℂ) := by
  have h1 := srcW_polar 1 0 one_pos one_pos γ
  have h2 := radial_log 1 0 1 (2 * γ / (1 : ℕ))
  rw [srcW_gauss, h2] at h1
  have hq : ∀ v : ℝ, qLog 1 v • angK (2 * γ * Real.exp (v / 2))
      = ((Real.exp (((0 : ℕ) + 1 : ℝ) * v - 1 * Real.exp v) : ℝ) : ℂ) *
          angK (2 * γ / ((1 : ℕ) : ℝ) * Real.exp (((1 : ℕ) : ℝ) * v / 2)) := by
    intro v
    rw [qLog, Real.Gamma_one, div_one, Complex.real_smul]
    congr 2
    · ring_nf
    · push_cast; ring_nf
  rw [integral_congr_ae (Eventually.of_forall hq)]
  have h3 : ∫ v : ℝ, ((Real.exp (((0 : ℕ) + 1 : ℝ) * v - 1 * Real.exp v) : ℝ) : ℂ) *
          angK (2 * γ / ((1 : ℕ) : ℝ) * Real.exp (((1 : ℕ) : ℝ) * v / 2))
      = 2 * ((π : ℂ) * cexp (-(γ : ℂ) ^ 2)) := by
    rw [h1]; ring
  rw [h3, Complex.ofReal_exp]
  push_cast
  ring

/-! ### Assembly -/

lemma srcW_log (d r : ℕ) (hd : 0 < d) {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    srcW d r a lam = (1 / 2 : ℂ) * ∫ v : ℝ, ((Real.exp ((r + 1) * v - a * Real.exp v) : ℝ) : ℂ) *
      angK (2 * lam / d * Real.exp (d * v / 2)) := by
  rw [srcW_polar d r hd ha lam, radial_log]

lemma log_shift (d r : ℕ) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ v : ℝ, ((Real.exp ((r + 1) * v - a * Real.exp v) : ℝ) : ℂ) * angK (c * Real.exp (d * v / 2))
      = (((a ^ (r + 1))⁻¹ : ℝ) : ℂ) * ∫ v : ℝ, ((Real.exp ((r + 1) * v - Real.exp v) : ℝ) : ℂ) *
          angK (c * Real.exp (-(d * Real.log a / 2)) * Real.exp (d * v / 2)) := by
  rw [← integral_sub_right_eq_self _ (Real.log a), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  have h1 : a * Real.exp (v - Real.log a) = Real.exp v := by
    rw [Real.exp_sub, Real.exp_log ha]; field_simp
  have h2 : Real.exp ((r + 1) * (v - Real.log a) - Real.exp v)
      = (a ^ (r + 1))⁻¹ * Real.exp ((r + 1) * v - Real.exp v) := by
    rw [show (r + 1 : ℝ) * (v - Real.log a) - Real.exp v
        = ((r + 1) * v - Real.exp v) + -(((r + 1 : ℕ) : ℝ) * Real.log a) by push_cast; ring,
      Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log ha]
    ring
  have h3 : c * Real.exp (d * (v - Real.log a) / 2)
      = c * Real.exp (-(d * Real.log a / 2)) * Real.exp (d * v / 2) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [h1, h2, h3]
  push_cast
  ring

lemma expect_logGamma (d r : ℕ) (c : ℝ) :
    ∫ v : ℝ, ((Real.exp ((r + 1) * v - Real.exp v) : ℝ) : ℂ) * angK (c * Real.exp (d * v / 2))
      = (r.factorial : ℂ) * ∫ y, angK (c * Real.exp (y / 2))
          ∂((logGammaLaw ((r : ℝ) + 1)).map (fun v => (d : ℝ) * v)) := by
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  rw [integral_map (by fun_prop) (by
      exact (continuous_angK.comp (by fun_prop)).aestronglyMeasurable),
    integral_logGammaLaw hr1, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  have hG : Real.Gamma ((r : ℝ) + 1) = r.factorial := Real.Gamma_nat_eq_factorial r
  rw [qLog, hG, Complex.real_smul]
  have hf : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  push_cast
  field_simp

lemma expect_law (d r : ℕ) (hd : 0 < d) (hr : r < d) (c : ℝ) :
    ∫ y, angK (c * Real.exp (y / 2)) ∂((logGammaLaw ((r : ℝ) + 1)).map (fun v => (d : ℝ) * v))
      = 2 * (π : ℂ) * (((∫ y, Real.exp (-(c ^ 2 * (d : ℝ) ^ d / 4) * Real.exp y)
          ∂(prodLaw (shapesD d r))) : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_logGammaLaw' (one_pos (α := ℝ))
  haveI := isProbabilityMeasure_prodLaw (shapesD d r) (shapesD_pos d r hd)
  set ν := prodLaw (shapesD d r)
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [law_eq d r hd hr, integral_map (by fun_prop) (by
      exact (continuous_angK.comp (by fun_prop)).aestronglyMeasurable),
    Measure.conv_comm]
  have hint : Integrable (fun z : ℝ => angK (c * Real.exp ((z + d * Real.log d) / 2)))
      (ν ∗ logGammaLaw 1) := by
    refine Integrable.of_bound ((continuous_angK.comp (by fun_prop)).aestronglyMeasurable)
      (2 * π) (Eventually.of_forall fun z => norm_angK_le _)
  have hR : (((∫ y, Real.exp (-(c ^ 2 * (d : ℝ) ^ d / 4) * Real.exp y) ∂ν) : ℝ) : ℂ)
      = ∫ y, ((Real.exp (-(c ^ 2 * (d : ℝ) ^ d / 4) * Real.exp y) : ℝ) : ℂ) ∂ν :=
    integral_ofReal.symm
  rw [integral_conv hint, hR, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_logGammaLaw one_pos]
  have hpt : ∀ x : ℝ, qLog 1 x • angK (c * Real.exp ((y + x + d * Real.log d) / 2))
      = qLog 1 x • angK (2 * (c * Real.exp ((y + d * Real.log d) / 2) / 2) *
          Real.exp (x / 2)) := by
    intro x
    congr 2
    rw [show 2 * (c * Real.exp ((y + d * Real.log d) / 2) / 2) * Real.exp (x / 2)
        = c * (Real.exp ((y + d * Real.log d) / 2) * Real.exp (x / 2)) by ring, ← Real.exp_add]
    congr 2; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), gauss_K]
  have hsq : (c * Real.exp ((y + d * Real.log d) / 2) / 2) ^ 2
      = c ^ 2 * (d : ℝ) ^ d / 4 * Real.exp y := by
    rw [div_pow, mul_pow, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * ((y + d * Real.log d) / 2)
        = y + d * Real.log d by push_cast; ring, Real.exp_add,
      show (d : ℝ) * Real.log d = ((d : ℕ) : ℝ) * Real.log d from rfl, Real.exp_nat_mul,
      Real.exp_log hdpos]
    ring
  rw [hsq]
  push_cast
  ring_nf

/-- **Proposition 4.1** (`prop:gamma`): for `d ≥ 2`, `r < d`, `a > 0` and real `λ`,
`𝒲_r(a; λ) = π r! a^{-r-1} E[exp(-λ² d^{d-2} a^{-d} S_r)]`, where
`E[f(S_r)] = ∫ f(e^y) d(prodLaw (shapesD d r))(y)`. -/
theorem srcW_gamma (d r : ℕ) (hd : 2 ≤ d) (hr : r < d) {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    srcW d r a lam = ((π * r.factorial / a ^ (r + 1) *
      ∫ y, Real.exp (-(lam ^ 2 * (d : ℝ) ^ (d - 2) / a ^ d) * Real.exp y)
        ∂(prodLaw (shapesD d r)) : ℝ) : ℂ) := by
  have hd0 : 0 < d := by omega
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
  rw [srcW_log d r hd0 ha, log_shift d r ha, expect_logGamma, expect_law d r hd0 hr]
  have hk : (2 * lam / d * Real.exp (-(d * Real.log a / 2))) ^ 2 * (d : ℝ) ^ d / 4
      = lam ^ 2 * (d : ℝ) ^ (d - 2) / a ^ d := by
    have hexp : Real.exp (-(d * Real.log a / 2)) ^ 2 = (a ^ d)⁻¹ := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -(d * Real.log a / 2)
          = -(((d : ℕ) : ℝ) * Real.log a) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log ha]
    have hdd : (d : ℝ) ^ d = (d : ℝ) ^ (d - 2) * (d : ℝ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [mul_pow, div_pow, mul_pow, hexp, hdd]
    field_simp
    ring
  rw [hk]
  push_cast
  field_simp

end Painleve
