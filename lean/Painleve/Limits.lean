import Painleve.Phi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace Painleve
open MeasureTheory Set Filter Topology

lemma gamma_refl : Real.Gamma (1 / 4) * Real.Gamma (3 / 4) = Real.pi * Real.sqrt 2 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring,
    Real.sin_pi_div_four] at h
  rw [h]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith [h2]

lemma gamma_five_quarter : Real.Gamma (5 / 4) = Real.Gamma (1 / 4) / 4 := by
  have h := Real.Gamma_add_one (s := 1 / 4) (by norm_num)
  rw [show (5 : ℝ) / 4 = 1 / 4 + 1 by norm_num, h]
  ring

lemma gamma_half_eq : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq

lemma gamma_three_half_eq : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, h, Real.Gamma_one_half_eq]
  ring

lemma sqrt_pi_half : Real.sqrt (Real.pi / 2) = Real.sqrt Real.pi / Real.sqrt 2 :=
  Real.sqrt_div Real.pi_pos.le 2

lemma sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

lemma sqrt_two_pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
  Real.sqrt_mul (by norm_num) Real.pi

theorem gamma_match0 :
    Real.sqrt (Real.pi / 2) * (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)) =
      Real.pi ^ 2 * Real.sqrt 8 / (4 * Real.Gamma (3 / 4) ^ 2) := by
  rw [sqrt_pi_half, sqrt_eight]
  have hG := gamma_refl
  have hr : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt Real.pi ≠ 0 := by positivity
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  have e1 : Real.sqrt Real.pi / Real.sqrt 2 * (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi))
      = Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt 2) := by
    field_simp
  rw [e1, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (4 * (Real.Gamma (1 / 4) * Real.Gamma (3 / 4) + Real.pi * Real.sqrt 2)) * hG

theorem gamma_match1 :
    -(Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi)) =
      -(Real.pi ^ 2 * Real.sqrt 2 / (4 * (Real.Gamma (3 / 4) * Real.Gamma (5 / 4)))) := by
  rw [sqrt_pi_half, sqrt_two_pi, gamma_five_quarter]
  have hG := gamma_refl
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  have hpos : Real.pi * Real.sqrt 2 ≠ 0 := by positivity
  have hL : Real.sqrt Real.pi / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt Real.pi) = Real.pi := by
    rw [show Real.sqrt Real.pi / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt Real.pi)
      = (Real.sqrt Real.pi * Real.sqrt Real.pi) * (Real.sqrt 2 / Real.sqrt 2) by ring,
      div_self hr0, mul_one, hpi]
  have hR : Real.pi ^ 2 * Real.sqrt 2 / (4 * (Real.Gamma (3 / 4) * (Real.Gamma (1 / 4) / 4)))
      = Real.pi := by
    rw [show 4 * (Real.Gamma (3 / 4) * (Real.Gamma (1 / 4) / 4)) = Real.Gamma (1 / 4) * Real.Gamma (3 / 4)
      by ring, hG, div_eq_iff hpos]
    ring
  rw [hL, hR]

theorem gamma_match2 :
    2 * Real.sqrt (Real.pi / 2) * (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi) =
      Real.pi ^ 2 / (2 * Real.sqrt 8 * Real.Gamma (5 / 4) ^ 2) := by
  rw [sqrt_pi_half, sqrt_eight, gamma_five_quarter]
  have hG := gamma_refl
  have hr : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt Real.pi ≠ 0 := by positivity
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  have e1 : 2 * (Real.sqrt Real.pi / Real.sqrt 2) * (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi)
      = 2 * Real.Gamma (3 / 4) ^ 2 / Real.sqrt 2 := by
    field_simp
  rw [e1, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (Real.sqrt 2 / 2 * (Real.Gamma (1 / 4) * Real.Gamma (3 / 4) + Real.pi * Real.sqrt 2)) * hG
    + (Real.sqrt 2 * Real.pi ^ 2 / 2) * hr

lemma beta_interval (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∫ t in (0 : ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (x : ℂ)) (t := (y : ℂ))
    (by simpa using hx) (by simpa using hy)
  have hint : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ ((x : ℂ) - 1) * (1 - (t : ℂ)) ^ ((y : ℂ) - 1)
      = ((∫ t in (0 : ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h0 : (0 : ℝ) ≤ t := ht.1
    have h1 : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow h0, Complex.ofReal_cpow h1,
      Complex.ofReal_sub, Complex.ofReal_one]
  unfold Complex.betaIntegral at h
  rw [hint, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at h
  have key : Real.Gamma x * Real.Gamma y =
      Real.Gamma (x + y) * ∫ t in (0 : ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
    exact_mod_cast h
  have hpos : 0 < Real.Gamma (x + y) := Real.Gamma_pos_of_pos (by linarith)
  rw [eq_div_iff hpos.ne']
  linear_combination (-1 : ℝ) * key

lemma beta_Ioi (x y : ℝ) (_hx : 0 < x) (_hy : 0 < y) :
    ∫ u in Ioi (0 : ℝ), u ^ (x - 1) * (1 + u) ^ (-(x + y)) =
      ∫ t in Ioo (0 : ℝ) 1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
  let f : ℝ → ℝ := fun t => t / (1 - t)
  have hf' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (1 / (1 - t) ^ 2) (Ioo 0 1) t := by
    intro t ht
    have h1 : (1 - t) ≠ 0 := (by linarith [ht.2] : (0 : ℝ) < 1 - t).ne'
    have := HasDerivAt.div (hasDerivAt_id t) ((hasDerivAt_id t).const_sub 1) h1
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id]
    congr 1
    ring
  have himg : f '' Ioo 0 1 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos ht.1 (by linarith [ht.2])
    · intro hu
      have hu' : (0 : ℝ) < u := hu
      have hu1 : (0 : ℝ) < 1 + u := by linarith
      refine ⟨u / (1 + u), ⟨div_pos hu hu1, (div_lt_one hu1).mpr (by linarith)⟩, ?_⟩
      simp only [f]
      have h2 : (1 : ℝ) - u / (1 + u) = 1 / (1 + u) := by field_simp; ring
      rw [h2]
      field_simp
  have hinj : InjOn f (Ioo 0 1) := by
    intro t1 ht1 t2 ht2 h
    simp only [f] at h
    have h1 : (1 - t1) ≠ 0 := (by linarith [ht1.2] : (0 : ℝ) < 1 - t1).ne'
    have h2 : (1 - t2) ≠ 0 := (by linarith [ht2.2] : (0 : ℝ) < 1 - t2).ne'
    field_simp at h
    linarith
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hinj
    (fun u : ℝ => u ^ (x - 1) * (1 + u) ^ (-(x + y)))
  rw [himg] at key
  rw [key]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 : (0 : ℝ) < t := ht.1
  have hr0 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  simp only [smul_eq_mul, f]
  rw [abs_of_pos (by positivity)]
  have e1 : 1 + t / (1 - t) = (1 - t)⁻¹ := by
    field_simp
    ring
  rw [e1, Real.inv_rpow hr0.le, Real.rpow_neg hr0.le, inv_inv, Real.div_rpow ht0.le hr0.le]
  have hpow : (1 - t) ^ (y - 1) = (1 - t) ^ (x + y) / (1 - t) ^ (x - 1) / (1 - t) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hr0, ← Real.rpow_sub hr0]
    congr 1
    push_cast
    ring
  rw [hpow]
  ring

lemma lemmaS (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∫ s in Ioi (0 : ℝ), s ^ (2 * x - 1) * (1 + s ^ 2) ^ (-(x + y)) =
      (1 / 2) * (Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)) := by
  have h2 := integral_comp_rpow_Ioi (fun u : ℝ => u ^ (x - 1) * (1 + u) ^ (-(x + y)))
    (p := 2) (by norm_num)
  have h3 : ∫ s in Ioi (0 : ℝ), (|(2 : ℝ)| * s ^ ((2 : ℝ) - 1)) •
      (fun u : ℝ => u ^ (x - 1) * (1 + u) ^ (-(x + y))) (s ^ (2 : ℝ))
      = ∫ s in Ioi (0 : ℝ), 2 * (s ^ (2 * x - 1) * (1 + s ^ 2) ^ (-(x + y))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := hs
    have hq : s ^ (2 * x - 1) = s * s ^ (2 * x - 2) := by
      rw [show 2 * x - 1 = 1 + (2 * x - 2) by ring, Real.rpow_add hs0, Real.rpow_one]
    have hp : (s ^ 2) ^ (x - 1) = s ^ (2 * x - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      congr 1
      push_cast
      ring
    simp only [smul_eq_mul, Real.rpow_two]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      hp, hq]
    ring
  have h4 := h3.symm.trans h2
  rw [integral_const_mul] at h4
  have hB : ∫ t in Ioo (0 : ℝ) 1, t ^ (x - 1) * (1 - t) ^ (y - 1) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact beta_interval x y hx hy
  rw [beta_Ioi x y hx hy, hB] at h4
  linarith

lemma integrableOn_of_integral_ne {f : ℝ → ℝ} {S : Set ℝ} (h : ∫ x in S, f x ≠ 0) :
    IntegrableOn f S := by
  by_contra hn
  exact h (integral_undef hn)

lemma tendsto_sq_half : Tendsto (fun a : ℝ => a ^ 2 / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun a : ℝ => a ^ 2 / 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2 / 2)) :=
      ((continuous_id.pow 2).div_const 2).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : (0 : ℝ) < a := ha
    show (0 : ℝ) < a ^ 2 / 2
    positivity

/-- Dominated convergence for the parameter `y → 0⁺` in `Phi α β y 1`. -/
lemma tendsto_Phi_gen (α β : ℝ)
    (hb : IntegrableOn (fun s : ℝ => s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))) (Ioi 0)) :
    Tendsto (fun y => Phi α β y 1) (𝓝[>] 0)
      (𝓝 (∫ s in Ioi (0 : ℝ), s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2)))) := by
  unfold Phi
  have hnn : ∀ s : ℝ, 0 < s → 0 ≤ s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2)) :=
    fun s hs => mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg (by nlinarith) _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))) ?_ ?_ hb ?_
  · exact Eventually.of_forall fun y => (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs
    show ‖Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))‖ ≤
      s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))
    have hF : Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2)) =
        Real.exp (-y * s) * (s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))) := by ring
    have hle : Real.exp (-y * s) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := mul_nonneg hy0.le hs0.le
      linarith)
    rw [hF, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hnn s hs0))]
    exact mul_le_of_le_one_left (hnn s hs0) hle
  · refine ae_of_all _ (fun s => ?_)
    have hc : Continuous (fun y : ℝ => Real.exp (-y * s) * s ^ (α - 1 / 2) *
        (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h

lemma integrable_b_of_pos (α β : ℝ) (h : ∫ s in Ioi (0 : ℝ), s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2)) ≠ 0) :
    IntegrableOn (fun s : ℝ => s ^ (α - 1 / 2) * (1 + 1 * s ^ 2) ^ (-(β + 1 / 2))) (Ioi 0) :=
  integrableOn_of_integral_ne h

lemma value_quarter :
    ∫ s in Ioi (0 : ℝ), s ^ ((0 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((0 : ℝ) + 1 / 2)) =
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi) := by
  have hconv : (fun s : ℝ => s ^ ((0 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((0 : ℝ) + 1 / 2))) =
      fun s => s ^ (2 * (1 / 4 : ℝ) - 1) * (1 + s ^ 2) ^ (-((1 / 4 : ℝ) + 1 / 4)) := by
    funext s
    norm_num
  rw [hconv, lemmaS (1 / 4) (1 / 4) (by norm_num) (by norm_num),
    show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num, gamma_half_eq]
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

lemma value_three_quarter :
    ∫ s in Ioi (0 : ℝ), s ^ ((1 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((1 : ℝ) + 1 / 2)) =
      Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi := by
  have hconv : (fun s : ℝ => s ^ ((1 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((1 : ℝ) + 1 / 2))) =
      fun s => s ^ (2 * (3 / 4 : ℝ) - 1) * (1 + s ^ 2) ^ (-((3 / 4 : ℝ) + 3 / 4)) := by
    funext s
    norm_num
  rw [hconv, lemmaS (3 / 4) (3 / 4) (by norm_num) (by norm_num),
    show (3 / 4 : ℝ) + 3 / 4 = 3 / 2 by norm_num, gamma_three_half_eq]
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

theorem tendsto_Phi00 :
    Tendsto (fun a : ℝ => Phi 0 0 (a ^ 2 / 2) 1) (𝓝[>] 0)
      (𝓝 (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi))) := by
  have hb : IntegrableOn (fun s : ℝ => s ^ ((0 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((0 : ℝ) + 1 / 2)))
      (Ioi 0) := by
    apply integrable_b_of_pos
    rw [value_quarter]
    have h1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)
    positivity
  have h := (tendsto_Phi_gen 0 0 hb).comp tendsto_sq_half
  rw [value_quarter] at h
  exact h

theorem tendsto_Phi11 :
    Tendsto (fun a : ℝ => Phi 1 1 (a ^ 2 / 2) 1) (𝓝[>] 0)
      (𝓝 (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi)) := by
  have hb : IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((1 : ℝ) + 1 / 2)))
      (Ioi 0) := by
    apply integrable_b_of_pos
    rw [value_three_quarter]
    have h1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
    have hpi : 0 < Real.sqrt Real.pi := by positivity
    positivity
  have h := (tendsto_Phi_gen 1 1 hb).comp tendsto_sq_half
  rw [value_three_quarter] at h
  exact h

lemma Phi10_subst (y : ℝ) (hy : 0 < y) :
    Phi 1 0 y 1 = y⁻¹ * ∫ x in Ioi (0 : ℝ), Real.exp (-y * ((1 / y) * x)) *
      ((1 / y) * x) ^ ((1 : ℝ) - 1 / 2) * (1 + 1 * ((1 / y) * x) ^ 2) ^ (-((0 : ℝ) + 1 / 2)) := by
  have h := integral_comp_mul_left_Ioi
    (fun s : ℝ => Real.exp (-y * s) * s ^ ((1 : ℝ) - 1 / 2) * (1 + 1 * s ^ 2) ^ (-((0 : ℝ) + 1 / 2)))
    0 (one_div_pos.mpr hy)
  rw [mul_zero] at h
  unfold Phi
  rw [h, smul_eq_mul, inv_div, div_one, ← mul_assoc, inv_mul_cancel₀ hy.ne', one_mul]

lemma pointwise_K (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    a * ((a ^ 2 / 2)⁻¹ * (Real.exp (-(a ^ 2 / 2) * ((1 / (a ^ 2 / 2)) * x)) *
      ((1 / (a ^ 2 / 2)) * x) ^ ((1 : ℝ) - 1 / 2) *
      (1 + 1 * ((1 / (a ^ 2 / 2)) * x) ^ 2) ^ (-((0 : ℝ) + 1 / 2)))) =
    Real.sqrt 2 * (Real.exp (-x) * x ^ ((1 : ℝ) / 2) * ((a ^ 2 / 2) ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2))) := by
  have hy : 0 < a ^ 2 / 2 := by positivity
  generalize hydef : a ^ 2 / 2 = y at hy ⊢
  have hy' : y ≠ 0 := hy.ne'
  have e1 : Real.exp (-y * ((1 / y) * x)) = Real.exp (-x) := by
    congr 1
    field_simp
  have e2 : ((1 / y) * x) ^ ((1 : ℝ) - 1 / 2) = x ^ ((1 : ℝ) / 2) / Real.sqrt y := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.mul_rpow (by positivity) hx.le,
      Real.div_rpow zero_le_one hy.le, Real.one_rpow, ← Real.sqrt_eq_rpow]
    ring
  have e3 : (1 + 1 * ((1 / y) * x) ^ 2) ^ (-((0 : ℝ) + 1 / 2)) =
      (y ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2)) * y := by
    have h1 : 1 + 1 * ((1 / y) * x) ^ 2 = (y ^ 2 + x ^ 2) * (y ^ 2)⁻¹ := by
      field_simp
    have h2 : ((y ^ 2)⁻¹) ^ (-((1 : ℝ) / 2)) = y := by
      rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
        ← Real.sqrt_eq_rpow, Real.sqrt_sq hy.le]
    rw [h1, show -((0 : ℝ) + 1 / 2) = -((1 : ℝ) / 2) by norm_num,
      Real.mul_rpow (by positivity) (by positivity), h2]
  have e4 : Real.sqrt y = a / Real.sqrt 2 := by
    rw [← hydef, Real.sqrt_div (by positivity), Real.sqrt_sq ha.le]
  rw [e1, e2, e3, e4]
  have hr : Real.sqrt 2 ≠ 0 := by positivity
  have ha' : a ≠ 0 := ha.ne'
  field_simp

lemma tendsto_K : Tendsto (fun y : ℝ => ∫ x in Ioi (0 : ℝ),
    Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (y ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2)))
    (𝓝[>] 0) (𝓝 (Real.sqrt Real.pi)) := by
  have hval : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (x ^ 2) ^ (-((1 : ℝ) / 2)) =
      Real.sqrt Real.pi := by
    rw [← gamma_half_eq, Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 1 / 2)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hq : (x ^ 2) ^ (-((1 : ℝ) / 2)) = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num [Real.rpow_neg_one]
    show Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (x ^ 2) ^ (-((1 : ℝ) / 2)) =
      Real.exp (-x) * x ^ ((1 : ℝ) / 2 - 1)
    rw [hq, Real.rpow_sub hx0, Real.rpow_one]
    ring
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (x ^ 2) ^ (-((1 : ℝ) / 2)))
      (Ioi 0) := integrableOn_of_integral_ne (by rw [hval]; exact hpi)
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (F := fun (y : ℝ) (x : ℝ) => Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (y ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2)))
    (f := fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (x ^ 2) ^ (-((1 : ℝ) / 2)))
    (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (x ^ 2) ^ (-((1 : ℝ) / 2))) ?_ ?_ hint ?_
  · rw [hval] at h
    exact h
  · exact Eventually.of_forall fun y => (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    show ‖Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (y ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2))‖ ≤
      Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (x ^ 2) ^ (-((1 : ℝ) / 2))
    have hnn : 0 ≤ Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (y ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2)) := by
      positivity
    rw [Real.norm_of_nonneg hnn]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg y]) (by norm_num)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have hc : Continuous (fun y : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) / 2) * (y ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2))) := by
      apply Continuous.mul continuous_const
      exact Continuous.rpow_const (by fun_prop) (fun y => Or.inl (by positivity))
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h

theorem tendsto_a_Phi10 :
    Tendsto (fun a : ℝ => a * Phi 1 0 (a ^ 2 / 2) 1) (𝓝[>] 0) (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have hK := (tendsto_K.comp tendsto_sq_half).const_mul (Real.sqrt 2)
  rw [← sqrt_two_pi] at hK
  refine hK.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : (0 : ℝ) < a := ha
  have hy : (0 : ℝ) < a ^ 2 / 2 := by positivity
  rw [Phi10_subst (a ^ 2 / 2) hy]
  calc Real.sqrt 2 * ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((1 : ℝ) / 2) *
          ((a ^ 2 / 2) ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2))
      = ∫ x in Ioi (0 : ℝ), Real.sqrt 2 * (Real.exp (-x) * x ^ ((1 : ℝ) / 2) *
          ((a ^ 2 / 2) ^ 2 + x ^ 2) ^ (-((1 : ℝ) / 2))) := (integral_const_mul _ _).symm
    _ = ∫ x in Ioi (0 : ℝ), a * ((a ^ 2 / 2)⁻¹ * (Real.exp (-(a ^ 2 / 2) * ((1 / (a ^ 2 / 2)) * x)) *
          ((1 / (a ^ 2 / 2)) * x) ^ ((1 : ℝ) - 1 / 2) *
          (1 + 1 * ((1 / (a ^ 2 / 2)) * x) ^ 2) ^ (-((0 : ℝ) + 1 / 2)))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : (0 : ℝ) < x := hx
        exact (pointwise_K a x ha' hx0).symm
    _ = a * ((a ^ 2 / 2)⁻¹ * ∫ x in Ioi (0 : ℝ), Real.exp (-(a ^ 2 / 2) * ((1 / (a ^ 2 / 2)) * x)) *
          ((1 / (a ^ 2 / 2)) * x) ^ ((1 : ℝ) - 1 / 2) *
          (1 + 1 * ((1 / (a ^ 2 / 2)) * x) ^ 2) ^ (-((0 : ℝ) + 1 / 2))) := by
        rw [integral_const_mul, integral_const_mul]

end Painleve
