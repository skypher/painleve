import Painleve.Source
import Painleve.Phi
import Painleve.Kernel
import Painleve.Moments
import Mathlib.Analysis.Calculus.ParametricIntegral

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace Painleve

/-- The integrand of `wsrc`. -/
noncomputable def Gint (r : ℕ) (a lam : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))

/-- The planar source with weight ‖z‖^{2r} and coupling λ. -/
noncomputable def wsrc (r : ℕ) (a lam : ℝ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))

lemma wsrc_eq_integral (r : ℕ) (a lam : ℝ) : wsrc r a lam = ∫ z : ℂ, Gint r a lam z := rfl

lemma re_arg (a lam : ℝ) (z : ℂ) :
    (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4)).re = -a * ‖z‖ ^ 2 := by
  have hph : ((I * lam / 4) * (z ^ 4 + conj z ^ 4)).re = 0 := by
    rw [show conj z ^ 4 = conj (z ^ 4) from (map_pow _ _ _).symm]
    exact phase_re lam (z ^ 4)
  rw [Complex.add_re, hph, add_zero]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma norm_Gint (r : ℕ) (a lam : ℝ) (z : ℂ) :
    ‖Gint r a lam z‖ = ‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) := by
  unfold Gint
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (norm_nonneg z) _),
    Complex.norm_exp, re_arg]

lemma norm_moment_density (r : ℕ) (a : ℝ) (z : ℂ) :
    ‖z ^ (2 * r) * conj z ^ 0 * density a z‖ = ‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) := by
  simp [norm_pow, norm_density]

lemma integrable_Gint (r : ℕ) (a lam : ℝ) (ha : 0 < a) : Integrable (Gint r a lam) := by
  refine Integrable.mono' (integrable_moment a ha (2 * r) 0).norm ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold Gint
    fun_prop
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_moment_density, norm_Gint]

/-- The `a`-derivative of the integrand: `∂_a G_r = -G_{r+1}`. -/
lemma hasDerivAt_Gint (r : ℕ) (lam : ℝ) (z : ℂ) (a : ℝ) :
    HasDerivAt (fun a : ℝ => Gint r a lam z) (-Gint (r + 1) a lam z) a := by
  unfold Gint
  have h1 : HasDerivAt (fun t : ℝ => -(t : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
      (I * lam / 4) * (z ^ 4 + conj z ^ 4)) (-((‖z‖ ^ 2 : ℝ) : ℂ)) a := by
    have := ((((hasDerivAt_id a).ofReal_comp).neg).mul_const ((‖z‖ ^ 2 : ℝ) : ℂ)).add_const
      ((I * lam / 4) * (z ^ 4 + conj z ^ 4))
    simpa using this
  have h2 := (h1.cexp).const_mul (((‖z‖ ^ (2 * r) : ℝ) : ℂ))
  refine h2.congr_deriv ?_
  have hp : ((‖z‖ ^ (2 * (r + 1)) : ℝ) : ℂ) = ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hp]
  ring

lemma continuous_Gint (r : ℕ) (a lam : ℝ) : Continuous (Gint r a lam) := by
  unfold Gint
  fun_prop

/-- Differentiation of the planar source with respect to `a`. -/
theorem hasDerivAt_wsrc (r : ℕ) (a0 lam : ℝ) (ha0 : 0 < a0) :
    HasDerivAt (fun a => wsrc r a lam) (-wsrc (r + 1) a0 lam) a0 := by
  have ha2 : 0 < a0 / 2 := by linarith
  have hb : Integrable (fun z : ℂ => ‖z ^ (2 * (r + 1)) * conj z ^ 0 * density (a0 / 2) z‖) :=
    (integrable_moment (a0 / 2) ha2 (2 * (r + 1)) 0).norm
  have hmeas : ∀ a : ℝ, AEStronglyMeasurable (fun z => Gint r a lam z) volume :=
    fun a => (continuous_Gint r a lam).aestronglyMeasurable
  have hmeas' : ∀ a : ℝ, AEStronglyMeasurable (fun z => -Gint (r + 1) a lam z) volume :=
    fun a => ((continuous_Gint (r + 1) a lam).neg).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂(volume : Measure ℂ), ∀ a' ∈ Ioi (a0 / 2),
      ‖-Gint (r + 1) a' lam z‖ ≤ ‖z ^ (2 * (r + 1)) * conj z ^ 0 * density (a0 / 2) z‖ := by
    refine Filter.Eventually.of_forall fun z a' ha' => ?_
    have ha'' : a0 / 2 < a' := ha'
    rw [norm_neg, norm_Gint, norm_moment_density]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg z) _)
    apply Real.exp_le_exp.mpr
    have hz : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    nlinarith
  have hdiff : ∀ᵐ z ∂(volume : Measure ℂ), ∀ a' ∈ Ioi (a0 / 2),
      HasDerivAt (fun a => Gint r a lam z) (-Gint (r + 1) a' lam z) a' :=
    Filter.Eventually.of_forall fun z a' _ => hasDerivAt_Gint r lam z a'
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun a z => Gint r a lam z)
    (F' := fun a z => -Gint (r + 1) a lam z) (x₀ := a0)
    (s := Ioi (a0 / 2)) (bound := fun z => ‖z ^ (2 * (r + 1)) * conj z ^ 0 * density (a0 / 2) z‖)
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun a => hmeas a)
    (integrable_Gint r a0 lam ha0)
    (hmeas' a0)
    hbound hb hdiff
  have h2 := key.2
  rw [integral_neg] at h2
  exact h2


/-- Derivative of `Φ` in the parameter `y`: `∂_y Φ(α,β;y,w) = -Φ(α+1,β;y,w)`. -/
theorem hasDerivAt_Phi_y (α β y w : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (hw : 0 < w) :
    HasDerivAt (fun y => Phi α β y w) (-Phi (α + 1) β y w) y := by
  have hy2 : 0 < y / 2 := by linarith
  have hyU : Ioi (y / 2) ∈ 𝓝 y := Ioi_mem_nhds (by linarith)
  have hbnd : IntegrableOn (fun s : ℝ => Real.exp (-(y / 2) * s) * s ^ (α + 1 - 1 / 2) *
      (1 + w * s ^ 2) ^ (-(β + 1 / 2))) (Ioi 0) :=
    integrableOn_kernel (y / 2) w (α + 1) β hy2 hw (by linarith)
  have hF_int := integrableOn_kernel y w α β hy hw hα
  have hbound : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y' ∈ Ioi (y / 2),
      ‖-(Real.exp (-y' * s) * s ^ (α + 1 - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2)))‖ ≤
        Real.exp (-(y / 2) * s) * s ^ (α + 1 - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs y' hy' => ?_)
    have hs0 : 0 < s := hs
    have hy'' : y / 2 < y' := hy'
    have hpos : 0 < 1 + w * s ^ 2 := by positivity
    have hpow : 0 ≤ s ^ (α + 1 - 1 / 2) := Real.rpow_nonneg hs0.le _
    have hB : 0 ≤ (1 + w * s ^ 2) ^ (-(β + 1 / 2)) := Real.rpow_nonneg hpos.le _
    have hE : Real.exp (-y' * s) ≤ Real.exp (-(y / 2) * s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hpow) hB)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hpow) hB
  have hdiff : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y' ∈ Ioi (y / 2),
      HasDerivAt (fun t => Real.exp (-t * s) * s ^ (α - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2)))
        (-(Real.exp (-y' * s) * s ^ (α + 1 - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2)))) y' := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs y' _ => ?_)
    have hs0 : 0 < s := hs
    have hpow : s ^ (α + 1 - 1 / 2) = s ^ (α - 1 / 2) * s := by
      rw [show α + 1 - 1 / 2 = (α - 1 / 2) + 1 by ring, Real.rpow_add hs0, Real.rpow_one]
    have h1 : HasDerivAt (fun t : ℝ => -t * s) (-1 * s) y' :=
      ((hasDerivAt_id' y').neg).mul_const s
    have h2 := (((h1.exp).mul_const (s ^ (α - 1 / 2))).mul_const
      ((1 + w * s ^ 2) ^ (-(β + 1 / 2))))
    refine h2.congr_deriv ?_
    rw [hpow]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y' s => Real.exp (-y' * s) * s ^ (α - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2)))
    (F' := fun y' s => -(Real.exp (-y' * s) * s ^ (α + 1 - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2))))
    (x₀ := y) (s := Ioi (y / 2))
    (bound := fun s => Real.exp (-(y / 2) * s) * s ^ (α + 1 - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2)))
    hyU
    (Filter.Eventually.of_forall fun y' => Measurable.aestronglyMeasurable (by fun_prop))
    hF_int
    (Measurable.aestronglyMeasurable (by fun_prop))
    hbound hbnd hdiff
  have h := key.2
  rw [integral_neg] at h
  unfold Phi
  exact h


/-- Chain rule: `∂_a Φ(α,β;a²/2,w) = -a Φ(α+1,β;a²/2,w)`. -/
lemma hasDerivAt_Phi_sq (α β w a0 : ℝ) (hα : 0 ≤ α) (ha0 : 0 < a0) (hw : 0 < w) :
    HasDerivAt (fun a => Phi α β (a ^ 2 / 2) w) (-Phi (α + 1) β (a0 ^ 2 / 2) w * a0) a0 := by
  have hsq : HasDerivAt (fun a : ℝ => a ^ 2 / 2) a0 a0 := by
    have h := (hasDerivAt_pow 2 a0).div_const 2
    rwa [show ((2 : ℕ) : ℝ) * a0 ^ (2 - 1) / 2 = a0 by norm_num] at h
  exact (hasDerivAt_Phi_y α β (a0 ^ 2 / 2) w hα (by positivity) hw).comp a0 hsq

/-- The integration-by-parts identity `y Φ(2,0) = ½Φ(1,0) + Φ(1,1)`. -/
lemma ibp_phi (y w : ℝ) (hy : 0 < y) (hw : 0 < w) :
    y * Phi 2 0 y w = (1 / 2) * Phi 1 0 y w + Phi 1 1 y w := by
  have e1 : Phi 2 0 y w = ∫ s in Set.Ioi (0 : ℝ),
      Real.exp (-y * s) * s ^ (3 / 2 : ℝ) * (1 + w * s ^ 2) ^ (-(1 / 2 : ℝ)) := by
    unfold Phi
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    norm_num
  have e2 : Phi 1 0 y w = ∫ s in Set.Ioi (0 : ℝ),
      Real.exp (-y * s) * s ^ (1 / 2 : ℝ) * (1 + w * s ^ 2) ^ (-(1 / 2 : ℝ)) := by
    unfold Phi
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    norm_num
  have e3 : Phi 1 1 y w = ∫ s in Set.Ioi (0 : ℝ),
      Real.exp (-y * s) * s ^ (1 / 2 : ℝ) * (1 + w * s ^ 2) ^ (-(3 / 2 : ℝ)) := by
    unfold Phi
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    norm_num
  rw [e1, e2, e3]
  exact ibp_kernel y w hy hw

/-- `wsrc 0` is the planar source with `y = a²/2`, `w = λ²`. -/
theorem wsrc_zero (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    wsrc 0 a lam = ((Real.sqrt (Real.pi / 2) * Phi 0 0 (a ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ) := by
  have hw0 : wsrc 0 a lam = ∫ z : ℂ,
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4)) := by
    unfold wsrc
    congr 1
    funext z
    simp
  have hR : ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(a ^ 2 / 2) * s) * s ^ (-(1 / 2) : ℝ) *
      (1 + lam ^ 2 * s ^ 2) ^ (-(1 / 2) : ℝ) = Phi 0 0 (a ^ 2 / 2) (lam ^ 2) := by
    unfold Phi
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    norm_num
  rw [hw0, planar_source a lam ha hlam, hR]

/-- `wsrc 1` in closed form. -/
theorem wsrc_one (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    wsrc 1 a lam = ((a * Real.sqrt (Real.pi / 2) * Phi 1 0 (a ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ) := by
  have hd := hasDerivAt_wsrc 0 a lam ha
  have hfun : (fun a' => wsrc 0 a' lam) =ᶠ[𝓝 a] (fun a' =>
      ((Real.sqrt (Real.pi / 2) * Phi 0 0 (a' ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ha) (fun a' ha' => wsrc_zero a' lam ha' hlam)
  have hc : HasDerivAt (fun a' => ((Real.sqrt (Real.pi / 2) * Phi 0 0 (a' ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ))
      (((Real.sqrt (Real.pi / 2) * (-Phi (0 + 1) 0 (a ^ 2 / 2) (lam ^ 2) * a) : ℝ) : ℂ)) a :=
    (((hasDerivAt_Phi_sq 0 0 (lam ^ 2) a le_rfl ha (by positivity)).const_mul
      (Real.sqrt (Real.pi / 2))).ofReal_comp)
  have hd' := hc.congr_of_eventuallyEq hfun
  have huniq := hd.unique hd'
  simp only [zero_add] at huniq
  have h2 : wsrc 1 a lam = -((((Real.sqrt (Real.pi / 2) * (-Phi 1 0 (a ^ 2 / 2) (lam ^ 2) * a) : ℝ)) : ℂ)) := by
    linear_combination -huniq
  rw [h2]
  push_cast
  ring

/-- `wsrc 2` in closed form. -/
theorem wsrc_two (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    wsrc 2 a lam = ((2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (a ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ) := by
  have hd := hasDerivAt_wsrc 1 a lam ha
  have hfun : (fun a' => wsrc 1 a' lam) =ᶠ[𝓝 a] (fun a' =>
      ((a' * Real.sqrt (Real.pi / 2) * Phi 1 0 (a' ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ha) (fun a' ha' => wsrc_one a' lam ha' hlam)
  have hc : HasDerivAt (fun a' => ((a' * Real.sqrt (Real.pi / 2) * Phi 1 0 (a' ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ))
      (((1 * Real.sqrt (Real.pi / 2) * Phi 1 0 (a ^ 2 / 2) (lam ^ 2) +
        a * Real.sqrt (Real.pi / 2) * (-Phi (1 + 1) 0 (a ^ 2 / 2) (lam ^ 2) * a) : ℝ) : ℂ)) a := by
    have h1 : HasDerivAt (fun a' : ℝ => a' * Real.sqrt (Real.pi / 2)) (1 * Real.sqrt (Real.pi / 2)) a :=
      (hasDerivAt_id' a).mul_const _
    have h2 := h1.mul (hasDerivAt_Phi_sq 1 0 (lam ^ 2) a (by norm_num) ha (by positivity))
    exact h2.ofReal_comp
  have hd' := hc.congr_of_eventuallyEq hfun
  have huniq := hd.unique hd'
  have hibp := ibp_phi (a ^ 2 / 2) (lam ^ 2) (by positivity) (by positivity)
  have hreal : (1 * Real.sqrt (Real.pi / 2) * Phi 1 0 (a ^ 2 / 2) (lam ^ 2) +
      a * Real.sqrt (Real.pi / 2) * (-Phi (1 + 1) 0 (a ^ 2 / 2) (lam ^ 2) * a))
      = -(2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (a ^ 2 / 2) (lam ^ 2)) := by
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    linear_combination (-(2 * Real.sqrt (Real.pi / 2))) * hibp
  rw [show (1 : ℕ) + 1 = 2 from rfl, hreal] at huniq
  have h2 : wsrc 2 a lam = -(((-(2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (a ^ 2 / 2) (lam ^ 2)) : ℝ) : ℂ)) := by
    linear_combination -huniq
  rw [h2]
  push_cast
  ring

/-- `wsrc 3` in closed form. -/
theorem wsrc_three (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    wsrc 3 a lam = ((2 * a * Real.sqrt (Real.pi / 2) * Phi 2 1 (a ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ) := by
  have hd := hasDerivAt_wsrc 2 a lam ha
  have hfun : (fun a' => wsrc 2 a' lam) =ᶠ[𝓝 a] (fun a' =>
      ((2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (a' ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ha) (fun a' ha' => wsrc_two a' lam ha' hlam)
  have hc : HasDerivAt (fun a' => ((2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (a' ^ 2 / 2) (lam ^ 2) : ℝ) : ℂ))
      (((2 * Real.sqrt (Real.pi / 2) * (-Phi (1 + 1) 1 (a ^ 2 / 2) (lam ^ 2) * a) : ℝ) : ℂ)) a :=
    (((hasDerivAt_Phi_sq 1 1 (lam ^ 2) a (by norm_num) ha (by positivity)).const_mul
      (2 * Real.sqrt (Real.pi / 2))).ofReal_comp)
  have hd' := hc.congr_of_eventuallyEq hfun
  have huniq := hd.unique hd'
  rw [show (2 : ℕ) + 1 = 3 from rfl] at huniq
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at huniq
  have h3 : wsrc 3 a lam = -(((2 * Real.sqrt (Real.pi / 2) * (-Phi 2 1 (a ^ 2 / 2) (lam ^ 2) * a) : ℝ) : ℂ)) := by
    linear_combination -huniq
  rw [h3]
  push_cast
  ring

end Painleve
