import Painleve.GammaRep
import Painleve.HankelSign

/-!
# Laplace transforms and negative moments of Gamma laws (for `cor:endpoint`)

For `G ~ Gamma(β)`: `E[e^{-cG}] = (1+c)^{-β}` (`c ≥ 0`) and
`E[G^{-s}] = Γ(β-s)/Γ(β)` (`s < β`); for a product of independent Gamma
variables the negative moments multiply.
-/

open MeasureTheory Set Filter
open scoped MeasureTheory

namespace Painleve

/-- `∫ e^{βv - e^v} dv = Γ(β)` (real form). -/
lemma integral_exp_log_Gamma {β : ℝ} (hβ : 0 < β) :
    ∫ v : ℝ, Real.exp (β * v - Real.exp v) = Real.Gamma β := by
  have h := integral_qLog hβ
  unfold qLog at h
  rw [integral_div, div_eq_one_iff_eq (Real.Gamma_pos_of_pos hβ).ne'] at h
  exact h

lemma integrable_exp_log_Gamma {β : ℝ} (hβ : 0 < β) :
    Integrable (fun v : ℝ => Real.exp (β * v - Real.exp v)) := by
  have h := (integrable_qLog hβ).const_mul (Real.Gamma β)
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [qLog]
  field_simp [(Real.Gamma_pos_of_pos hβ).ne']

/-- `E[e^{-cG}] = (1+c)^{-β}`. -/
theorem laplace_logGamma {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, Real.exp (-c * Real.exp x) ∂(logGammaLaw β) = (1 + c) ^ (-β) := by
  have h1c : 0 < 1 + c := by linarith
  set L := Real.log (1 + c) with hL
  rw [integral_logGammaLaw hβ]
  have hpt : ∀ x : ℝ, qLog β x • Real.exp (-c * Real.exp x)
      = Real.exp (β * x - (1 + c) * Real.exp x) / Real.Gamma β := by
    intro x
    rw [smul_eq_mul, qLog, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2; ring
  simp_rw [hpt]
  rw [integral_div, ← integral_sub_right_eq_self _ L]
  have hpt2 : ∀ x : ℝ, Real.exp (β * (x - L) - (1 + c) * Real.exp (x - L))
      = Real.exp (-β * L) * Real.exp (β * x - Real.exp x) := by
    intro x
    have he : Real.exp (x - L) = Real.exp x / (1 + c) := by
      rw [Real.exp_sub, hL, Real.exp_log h1c]
    rw [he, show (1 + c) * (Real.exp x / (1 + c)) = Real.exp x by field_simp, ← Real.exp_add]
    congr 1; ring
  simp_rw [hpt2]
  rw [integral_const_mul, integral_exp_log_Gamma hβ, Real.rpow_def_of_pos h1c, ← hL]
  field_simp [(Real.Gamma_pos_of_pos hβ).ne']

lemma integrable_exp_neg_mul_logGamma {β s : ℝ} (hb : 0 < β) (hs : s < β) :
    Integrable (fun x => Real.exp (-s * x)) (logGammaLaw β) := by
  have hβ : 0 < β - s := by linarith
  unfold logGammaLaw
  rw [integrable_withDensity_iff_integrable_smul₀' (measurable_qLog β).ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have h := (integrable_exp_log_Gamma hβ).div_const (Real.Gamma β)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (qLog_nonneg hb x), qLog, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2; ring

/-- `E[G^{-s}] = Γ(β-s)/Γ(β)` in logarithmic coordinates. -/
theorem moment_logGamma {β s : ℝ} (hb : 0 < β) (hs : s < β) :
    ∫ x, Real.exp (-s * x) ∂(logGammaLaw β) = Real.Gamma (β - s) / Real.Gamma β := by
  have hβ : 0 < β - s := by linarith
  rw [integral_logGammaLaw hb, ← integral_exp_log_Gamma hβ, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [qLog, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2; ring

/-- Negative moments multiply over independent factors. -/
theorem moment_prodLaw (s : ℝ) :
    ∀ (βs : List ℝ), (∀ b ∈ βs, 0 < b) → (∀ b ∈ βs, s < b) →
      Integrable (fun y => Real.exp (-s * y)) (prodLaw βs) ∧
      ∫ y, Real.exp (-s * y) ∂(prodLaw βs)
        = (βs.map fun b => Real.Gamma (b - s) / Real.Gamma b).prod
  | [], _, _ => by
    refine ⟨?_, ?_⟩
    · rw [prodLaw]; exact integrable_dirac enorm_lt_top
    · simp [prodLaw]
  | β :: βs, h, hs => by
    have hβ : 0 < β := h β (by simp)
    have hβs : ∀ b ∈ βs, 0 < b := fun b hb => h b (by simp [hb])
    have hsβ : s < β := hs β (by simp)
    have hsβs : ∀ b ∈ βs, s < b := fun b hb => hs b (by simp [hb])
    haveI := isProbabilityMeasure_logGammaLaw' hβ
    haveI := isProbabilityMeasure_prodLaw βs hβs
    obtain ⟨hI, hE⟩ := moment_prodLaw s βs hβs hsβs
    have hI0 := integrable_exp_neg_mul_logGamma hβ hsβ
    have hfac : ∀ x y : ℝ, Real.exp (-s * (x + y)) = Real.exp (-s * x) * Real.exp (-s * y) := by
      intro x y; rw [← Real.exp_add]; ring_nf
    have hint : Integrable (fun z => Real.exp (-s * z)) (logGammaLaw β ∗ prodLaw βs) := by
      rw [integrable_conv_iff (by fun_prop)]
      refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
      · simp_rw [hfac]; exact hI.const_mul _
      · have : (fun x => ∫ y, ‖Real.exp (-s * (x + y))‖ ∂(prodLaw βs))
            = fun x => Real.exp (-s * x) * ∫ y, Real.exp (-s * y) ∂(prodLaw βs) := by
          funext x
          simp_rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hfac]
          rw [integral_const_mul]
        rw [this]
        exact hI0.mul_const _
    refine ⟨by rw [prodLaw]; exact hint, ?_⟩
    rw [prodLaw, integral_conv hint]
    simp_rw [hfac]
    simp only [integral_const_mul]
    rw [integral_mul_const, moment_logGamma hβ hsβ, hE]
    simp

end Painleve
