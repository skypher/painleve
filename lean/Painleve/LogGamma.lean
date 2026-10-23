import Painleve.GaussMultC
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Laws of logarithms of Gamma variables

If `G` has the Gamma distribution with shape `β > 0`, then `log G` has the
density `q_β(v) = e^{βv - e^v}/Γ(β)` on `ℝ` (`lem:hankel-signs`). We define
this law, the laws of sums of independent such logarithms (convolutions), and
compute their characteristic functions: `E[e^{it log G}] = Γ(β+it)/Γ(β)`.
-/

open MeasureTheory Set Filter
open scoped MeasureTheory

namespace Painleve

/-- Substitution `y = e^x` on the whole line. -/
lemma integral_exp_smul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x, Real.exp x • g (Real.exp x) = ∫ y in Ioi 0, g y := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  rw [h, Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [abs_of_pos (Real.exp_pos x)]

lemma integrable_exp_smul_comp_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    Integrable (fun x => Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  rw [h, integrableOn_univ]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [abs_of_pos (Real.exp_pos x)]

lemma gammaIntegrand_log (s : ℂ) (v : ℝ) :
    Real.exp v • ((↑(Real.exp (-(Real.exp v))) : ℂ) * ((Real.exp v : ℝ) : ℂ) ^ (s - 1))
      = Complex.exp (s * v - Real.exp v) := by
  have hne : ((Real.exp v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos v).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp,
    Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- `∫ e^{sv - e^v} dv = Γ(s)` for `Re s > 0`. -/
theorem integral_cexp_log_Gamma {s : ℂ} (hs : 0 < s.re) :
    ∫ v : ℝ, Complex.exp (s * v - Real.exp v) = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, ← integral_exp_smul_comp]
  exact integral_congr_ae (Eventually.of_forall fun v => (gammaIntegrand_log s v).symm)

theorem integrable_cexp_log_Gamma {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun v : ℝ => Complex.exp (s * v - Real.exp v)) := by
  have h := (integrable_exp_smul_comp_iff
    (fun x : ℝ => (↑(Real.exp (-x)) : ℂ) * (x : ℂ) ^ (s - 1))).mpr
    (Complex.GammaIntegral_convergent hs)
  exact h.congr (Eventually.of_forall fun v => gammaIntegrand_log s v)

/-- The density `q_β(v) = e^{βv - e^v}/Γ(β)` of `log G`, `G ~ Gamma(β)`. -/
noncomputable def qLog (β v : ℝ) : ℝ := Real.exp (β * v - Real.exp v) / Real.Gamma β

lemma qLog_pos {β : ℝ} (hβ : 0 < β) (v : ℝ) : 0 < qLog β v :=
  div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hβ)

lemma qLog_nonneg {β : ℝ} (hβ : 0 < β) (v : ℝ) : 0 ≤ qLog β v := (qLog_pos hβ v).le

lemma measurable_qLog (β : ℝ) : Measurable (qLog β) := by
  unfold qLog; fun_prop

lemma ofReal_qLog (β v : ℝ) :
    ((qLog β v : ℝ) : ℂ) = Complex.exp ((β : ℂ) * v - Real.exp v) / (Real.Gamma β : ℂ) := by
  unfold qLog
  push_cast
  rfl

theorem integrable_qLog {β : ℝ} (hβ : 0 < β) : Integrable (qLog β) := by
  have h := integrable_cexp_log_Gamma (s := (β : ℂ)) (by simpa using hβ)
  have h2 : Integrable (fun v : ℝ => (Real.exp (β * v - Real.exp v) : ℝ)) := by
    have := h.re
    refine this.congr (Eventually.of_forall fun v => ?_)
    show (Complex.exp ((β : ℂ) * (v : ℂ) - ((Real.exp v : ℝ) : ℂ))).re = _
    rw [show (β : ℂ) * (v : ℂ) - ((Real.exp v : ℝ) : ℂ) = ((β * v - Real.exp v : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp, Complex.ofReal_re]
  exact h2.div_const _

theorem integral_qLog {β : ℝ} (hβ : 0 < β) : ∫ v, qLog β v = 1 := by
  have h := integral_cexp_log_Gamma (s := (β : ℂ)) (by simpa using hβ)
  have hG : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
  have h2 : ∫ v : ℝ, Real.exp (β * v - Real.exp v) = Real.Gamma β := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← Complex.Gamma_ofReal, ← h]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  unfold qLog
  rw [integral_div, h2, div_self hG]

/-- The law of `log G`, `G ~ Gamma(β)`. -/
noncomputable def logGammaLaw (β : ℝ) : Measure ℝ :=
  volume.withDensity fun v => ENNReal.ofReal (qLog β v)

instance isProbabilityMeasure_logGammaLaw {β : ℝ} [Fact (0 < β)] :
    IsProbabilityMeasure (logGammaLaw β) := by
  have hβ : 0 < β := Fact.out
  constructor
  rw [logGammaLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_qLog hβ)
      (Eventually.of_forall (qLog_nonneg hβ)), integral_qLog hβ, ENNReal.ofReal_one]

lemma isProbabilityMeasure_logGammaLaw' {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (logGammaLaw β) := by
  haveI : Fact (0 < β) := ⟨hβ⟩
  infer_instance

/-- Integration against `logGammaLaw β` is integration against the density. -/
lemma integral_logGammaLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : ℝ}
    (hβ : 0 < β) (g : ℝ → E) :
    ∫ v, g v ∂(logGammaLaw β) = ∫ v, qLog β v • g v := by
  have hm : Measurable fun v => (qLog β v).toNNReal :=
    (measurable_qLog β).real_toNNReal
  have := integral_withDensity_eq_integral_smul (μ := volume) hm g
  have heq : (fun v => ENNReal.ofReal (qLog β v)) = fun v => ((qLog β v).toNNReal : ENNReal) :=
    rfl
  rw [logGammaLaw, heq, this]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (qLog_nonneg hβ v)]

/-- `E[e^{it log G}] = Γ(β + it)/Γ(β)`. -/
theorem charFun_logGammaLaw {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    charFun (logGammaLaw β) t = Complex.Gamma (β + t * Complex.I) / Complex.Gamma β := by
  rw [charFun_apply_real, integral_logGammaLaw hβ]
  have hre : 0 < ((β : ℂ) + t * Complex.I).re := by simpa using hβ
  rw [← integral_cexp_log_Gamma hre, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [Complex.real_smul, ofReal_qLog, ← Complex.Gamma_ofReal, div_mul_eq_mul_div,
    ← Complex.exp_add]
  congr 2
  ring

/-- The law of `∑ log G_j` for independent Gamma variables with the listed
shapes: an iterated convolution. -/
noncomputable def prodLaw : List ℝ → Measure ℝ
  | [] => Measure.dirac 0
  | β :: βs => logGammaLaw β ∗ prodLaw βs

lemma isProbabilityMeasure_prodLaw :
    ∀ (βs : List ℝ), (∀ β ∈ βs, 0 < β) → IsProbabilityMeasure (prodLaw βs)
  | [], _ => by rw [prodLaw]; infer_instance
  | β :: βs, h => by
    rw [prodLaw]
    haveI := isProbabilityMeasure_logGammaLaw' (h β (by simp))
    haveI := isProbabilityMeasure_prodLaw βs (fun b hb => h b (by simp [hb]))
    infer_instance

theorem charFun_prodLaw :
    ∀ (βs : List ℝ), (∀ β ∈ βs, 0 < β) → ∀ t : ℝ,
      charFun (prodLaw βs) t =
        (βs.map fun β : ℝ => Complex.Gamma ((β : ℂ) + t * Complex.I) / Complex.Gamma (β : ℂ)).prod
  | [], _, t => by simp [prodLaw, charFun_apply_real]
  | β :: βs, h, t => by
    have hβ : 0 < β := h β (by simp)
    have hβs : ∀ b ∈ βs, 0 < b := fun b hb => h b (by simp [hb])
    haveI := isProbabilityMeasure_logGammaLaw' hβ
    haveI := isProbabilityMeasure_prodLaw βs hβs
    rw [prodLaw, charFun_conv, charFun_logGammaLaw hβ, charFun_prodLaw βs hβs t]
    simp

end Painleve
