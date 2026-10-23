import Painleve.StatementD
import Painleve.LogGamma
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The weighted sources in polar coordinates

`𝒲_r(a; λ) = ∫ |z|^{2r} exp(-a|z|² + (iλ/d)(z^d + z̄^d)) dA` (Section 3 of
`paper.tex`). In polar coordinates `z = R e^{iθ}` one has
`z^d + z̄^d = 2R^d cos(dθ)`, and the angular integral of `e^{iy cos(dθ)}` over a
period equals `K(y) = ∫_{-π}^{π} e^{iy cos θ} dθ` (Step 1 of `prop:gamma`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate Real

namespace Painleve

/-- `K(y) = ∫_{-π}^{π} e^{i y cos θ} dθ`, i.e. `2π J₀(y)`. -/
noncomputable def angK (y : ℝ) : ℂ := ∫ θ in (-π)..π, cexp (↑(y * Real.cos θ) * I)

lemma norm_angK_le (y : ℝ) : ‖angK y‖ ≤ 2 * π := by
  unfold angK
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π) (C := 1)
    (f := fun θ => cexp (↑(y * Real.cos θ) * I)) (fun θ _ => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have hab : |π - -π| = 2 * π := by rw [abs_of_pos (by linarith [Real.pi_pos])]; ring
  rw [hab, one_mul] at h
  exact h

lemma continuous_angK : Continuous angK := by
  unfold angK
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) _ _

lemma measurable_angK : Measurable angK := continuous_angK.measurable

/-- The angular integral over a period does not see the factor `d` in `cos(dθ)`. -/
lemma angular_dfold (d : ℕ) (hd : 0 < d) (y : ℝ) :
    ∫ θ in (-π)..π, cexp (↑(y * Real.cos (d * θ)) * I) = angK y := by
  set g : ℝ → ℂ := fun θ => cexp (↑(y * Real.cos θ) * I) with hg
  have hper : Function.Periodic g (2 * π) := by
    intro θ; simp only [hg, Real.cos_add_two_pi]
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h1 : ∫ θ in (-π)..π, g (d * θ) = (d : ℝ)⁻¹ • ∫ θ in (d * -π)..(d * π), g θ :=
    intervalIntegral.integral_comp_mul_left (f := g) hd'
  have h2 : ∫ θ in (d * -π)..(d * π), g θ = (d : ℤ) • ∫ θ in (-π)..π, g θ := by
    have := hper.intervalIntegral_add_zsmul_eq (d : ℤ) (d * -π)
      (fun t₁ t₂ => hcont.intervalIntegrable t₁ t₂)
    rw [show (d : ℝ) * -π + (d : ℤ) • (2 * π) = d * π by
      rw [zsmul_eq_mul]; push_cast; ring] at this
    rw [this, hper.intervalIntegral_add_eq (d * -π) (-π)]
    congr 2; ring
  show ∫ θ in (-π)..π, g (d * θ) = ∫ θ in (-π)..π, g θ
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [h1, h2, zsmul_eq_mul, Complex.real_smul]
  push_cast
  field_simp

/-- The weighted source `𝒲_r(a; λ)`. -/
noncomputable def srcW (d r : ℕ) (a lam : ℝ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    cexp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / d) * (z ^ d + conj z ^ d))

lemma momentD_eq_srcW (d : ℕ) (a : ℝ) (j : ℕ) : momentD d a j = srcW d j a 1 := by
  unfold momentD srcW densityD
  congr 1; ext z; congr 3; push_cast; ring

/-- `z^d + z̄^d = 2 R^d cos(dθ)` for `z = R e^{iθ}`. -/
lemma polar_pow_add_conj (d : ℕ) (R θ : ℝ) :
    ((R : ℂ) * (Real.cos θ + Real.sin θ * I)) ^ d
        + conj (((R : ℂ) * (Real.cos θ + Real.sin θ * I)) ^ d)
      = ((2 * R ^ d * Real.cos (d * θ) : ℝ) : ℂ) := by
  have h : ((R : ℂ) * (Real.cos θ + Real.sin θ * I)) ^ d
      = (R : ℂ) ^ d * (Complex.cos (d * θ) + Complex.sin (d * θ) * I) := by
    rw [mul_pow, Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos_add_sin_mul_I_pow]
  rw [h, map_mul, map_pow, Complex.conj_ofReal, map_add, map_mul, Complex.conj_I,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

/-- The polar form of the integrand (with the Jacobian `R`). -/
lemma srcW_integrand_polar (d r : ℕ) (a lam R θ : ℝ) (hR : 0 < R) :
    R • (((‖(Complex.polarCoord.symm (R, θ))‖ ^ (2 * r) : ℝ) : ℂ) *
      cexp (-(a : ℂ) * ((‖(Complex.polarCoord.symm (R, θ))‖ ^ 2 : ℝ) : ℂ)
        + (I * lam / d) * ((Complex.polarCoord.symm (R, θ)) ^ d
          + conj (Complex.polarCoord.symm (R, θ)) ^ d)))
      = ((R ^ (2 * r + 1) * Real.exp (-a * R ^ 2) : ℝ) : ℂ) *
          cexp (↑((2 * lam / d * R ^ d) * Real.cos (d * θ)) * I) := by
  rw [Complex.norm_polarCoord_symm, abs_of_pos hR, Complex.polarCoord_symm_apply, ← map_pow,
    polar_pow_add_conj]
  simp only
  rw [Complex.real_smul, show -(a : ℂ) * ((R ^ 2 : ℝ) : ℂ)
      + I * lam / d * ((2 * R ^ d * Real.cos (d * θ) : ℝ) : ℂ)
      = ((-a * R ^ 2 : ℝ) : ℂ) + ↑((2 * lam / d * R ^ d) * Real.cos (d * θ)) * I by
      push_cast; ring, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

lemma integrableOn_radial (r : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun R : ℝ => R ^ (2 * r + 1) * Real.exp (-a * R ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha (s := ((2 * r + 1 : ℕ) : ℝ))
    (by have : (0 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  refine h.congr_fun (fun R hR => ?_) measurableSet_Ioi
  simp only
  rw [Real.rpow_natCast]

/-- **Step 1 of `prop:gamma`**: the planar integral as a radial integral of `K`. -/
theorem srcW_polar (d r : ℕ) (hd : 0 < d) {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    srcW d r a lam = ∫ R in Ioi (0 : ℝ),
      ((R ^ (2 * r + 1) * Real.exp (-a * R ^ 2) : ℝ) : ℂ) * angK (2 * lam / d * R ^ d) := by
  set f : ℂ → ℂ := fun z => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    cexp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / d) * (z ^ d + conj z ^ d)) with hf
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hb : Integrable (fun p : ℝ × ℝ => (p.1 ^ (2 * r + 1) * Real.exp (-a * p.1 ^ 2)) * 1)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      refine Integrable.mul_prod (f := fun R : ℝ => R ^ (2 * r + 1) * Real.exp (-a * R ^ 2))
        (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_radial r ha) ?_
      exact integrable_const _
    rw [IntegrableOn, ← Measure.prod_restrict]
    refine hb.mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hf, Complex.polarCoord_symm_apply]
      fun_prop
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
      obtain ⟨R, θ⟩ := p
      obtain ⟨hR, -⟩ := hp
      have hR' : 0 < R := hR
      have := srcW_integrand_polar d r a lam R θ hR'
      simp only [hf] at this ⊢
      rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e1 : srcW d r a lam
      = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, p.1 • f (Complex.polarCoord.symm p) := by
    rw [srcW, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  rw [e1, Measure.volume_eq_prod, setIntegral_prod _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun R hR => ?_)
  have hR' : 0 < R := hR
  have hc : ∀ θ, R • f (Complex.polarCoord.symm (R, θ))
      = ((R ^ (2 * r + 1) * Real.exp (-a * R ^ 2) : ℝ) : ℂ) *
          cexp (↑((2 * lam / d * R ^ d) * Real.cos (d * θ)) * I) :=
    fun θ => srcW_integrand_polar d r a lam R θ hR'
  simp only
  simp_rw [hc]
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), angular_dfold d hd]

end Painleve
