import Painleve.Ibp
import Painleve.DiffInt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace Painleve
open Complex MeasureTheory
open scoped ComplexConjugate ContDiff

/-- The a-derivative of the density: `∂_a ρ_a(z) = -|z|² ρ_a(z)`. -/
lemma hasDerivAt_density_real (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => density s z) (-(z * conj z) * density t z) t := by
  have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ)) * (z * conj z) + (I / 4) * (z ^ 4 + conj z ^ 4))
      (-(z * conj z)) t := by
    have := ((((hasDerivAt_id t).ofReal_comp).neg).mul_const (z * conj z)).add_const
      ((I / 4) * (z ^ 4 + conj z ^ 4))
    simpa using this
  have hfun : (fun s : ℝ => density s z) = fun s : ℝ =>
      Complex.exp (-((s : ℂ)) * (z * conj z) + (I / 4) * (z ^ 4 + conj z ^ 4)) := by
    funext s
    rw [density_eq]
  rw [hfun]
  refine h1.cexp.congr_deriv ?_
  rw [density_eq]
  ring

/-- Iterated a-derivatives of the density: `∂_a^j ρ_a(z) = (-|z|²)^j ρ_a(z)`. -/
lemma iteratedDeriv_density (z : ℂ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => density s z) t = (-(z * conj z)) ^ j * density t z := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv j (fun s : ℝ => density s z) =
        fun s => (-(z * conj z)) ^ j * density s z := funext fun s => ih s
    rw [hfun, ((hasDerivAt_density_real z t).const_mul ((-(z * conj z)) ^ j)).deriv]
    ring

lemma contDiff_density (x : ℂ) : ContDiff ℝ ∞ (fun t : ℝ => density t x) := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  simp only [density_eq]
  fun_prop

lemma aestronglyMeasurable_iter (j : ℕ) (t : ℝ) :
    AEStronglyMeasurable (fun x : ℂ => iteratedDeriv j (fun s : ℝ => density s x) t) volume := by
  have hfun : (fun x : ℂ => iteratedDeriv j (fun s : ℝ => density s x) t) =
      fun x : ℂ => (-(x * conj x)) ^ j * density t x :=
    funext fun x => iteratedDeriv_density x j t
  rw [hfun]
  apply Continuous.aestronglyMeasurable
  unfold density
  fun_prop

lemma norm_neg_mul_conj_pow (x : ℂ) (j : ℕ) :
    ‖(-(x * conj x)) ^ j‖ = ‖x‖ ^ (2 * j) := by
  rw [norm_pow, norm_neg, norm_mul, Complex.norm_conj]
  ring

lemma iteratedDeriv_density_bound (a : ℝ) (_ha : 0 < a) (k : ℕ) (j : ℕ) (_hj : j ≤ k)
    (t : ℝ) (ht : t ∈ Metric.ball a (a / 2)) (x : ℂ) :
    ‖iteratedDeriv j (fun s : ℝ => density s x) t‖ ≤ ‖x ^ j * conj x ^ j * density (a / 2) x‖ := by
  have hta : a / 2 ≤ t := by
    have h := Metric.mem_ball.mp ht
    rw [Real.dist_eq] at h
    have := (abs_lt.mp h).1
    linarith
  have hL : ‖iteratedDeriv j (fun s : ℝ => density s x) t‖ =
      ‖x‖ ^ (2 * j) * Real.exp (-t * ‖x‖ ^ 2) := by
    rw [iteratedDeriv_density, norm_mul, norm_neg_mul_conj_pow, norm_density]
  have hR : ‖x ^ j * conj x ^ j * density (a / 2) x‖ =
      ‖x‖ ^ j * ‖x‖ ^ j * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_density]
  rw [hL, hR, two_mul, pow_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have := mul_nonneg (sub_nonneg.mpr hta) (sq_nonneg ‖x‖)
  nlinarith

/-- The planar function `h(a) = ∫_ℂ ρ_a`. -/
noncomputable def hPlanar (a : ℝ) : ℂ := ∫ z : ℂ, density a z

theorem iteratedDeriv_hPlanar (k : ℕ) (a : ℝ) (ha : 0 < a) :
    iteratedDeriv k hPlanar a = (-1 : ℂ) ^ k * mom a k k := by
  have key := iteratedDeriv_integral (μ := volume) (fun t z => density t z) (t₀ := a) (ε := a / 2)
    (half_pos ha) k (fun x => contDiff_density x)
    (fun j _ t => aestronglyMeasurable_iter j t)
    (fun j x => ‖x ^ j * conj x ^ j * density (a / 2) x‖)
    (fun j _ => (integrable_moment (a / 2) (half_pos ha) j j).norm)
    (fun j hj t ht x => iteratedDeriv_density_bound a ha k j hj t ht x) a
    (Metric.mem_ball_self (half_pos ha))
  unfold hPlanar
  rw [key]
  have hpt : ∫ x : ℂ, iteratedDeriv k (fun t : ℝ => density t x) a =
      ∫ x : ℂ, (-1 : ℂ) ^ k * (x ^ k * conj x ^ k * density a x) := by
    congr 1
    funext x
    rw [iteratedDeriv_density]
    ring
  rw [hpt, integral_const_mul]
  rfl

theorem hPlanar_ode (a : ℝ) (ha : 0 < a) :
    iteratedDeriv 3 hPlanar a + (a : ℂ) ^ 2 * deriv hPlanar a + (a : ℂ) * hPlanar a = 0 := by
  have hR0 : conj (mom a 0 0) = mom a 0 0 := by
    unfold mom
    rw [conj_moment a 0 0]
    simp
  have hR1 : conj (mom a 1 1) = mom a 1 1 := by
    unfold mom
    rw [conj_moment a 1 1]
    simp only [pow_one]
    rw [mul_comm (conj eta) eta, eta_mul_conj_eta, one_mul]
  have hA : mom a 0 0 + I * mom a 4 0 = (a : ℂ) * mom a 1 1 := by
    have h := moment_ibp a ha 1 0
    simpa using h
  have hB : I * mom a 3 3 = (a : ℂ) * mom a 0 4 := by
    have h := moment_ibp a ha 0 3
    simpa using h
  have hC : conj (mom a 0 4) = -mom a 4 0 := by
    unfold mom
    rw [conj_moment a 4 0, conj_eta_pow_four]
    simp
  have hA2 : mom a 0 0 + (-I) * conj (mom a 4 0) = (a : ℂ) * mom a 1 1 := by
    have h := congrArg (starRingEnd ℂ) hA
    simp only [map_add, map_mul, conj_I, conj_ofReal, hR0, hR1] at h
    exact h
  have hC2 : mom a 0 4 = -conj (mom a 4 0) := by
    have h := congrArg (starRingEnd ℂ) hC
    simp only [conj_conj, map_neg] at h
    exact h
  have hM33 : mom a 3 3 = (a : ℂ) * mom a 0 0 - (a : ℂ) ^ 2 * mom a 1 1 := by
    linear_combination (-I) * hB + (-(I * (a : ℂ))) * hC2 + (-(a : ℂ)) * hA2 +
      mom a 3 3 * Complex.I_sq
  have h3 : iteratedDeriv 3 hPlanar a = -mom a 3 3 := by
    rw [iteratedDeriv_hPlanar 3 a ha]
    norm_num
  have h1 : deriv hPlanar a = -mom a 1 1 := by
    rw [← iteratedDeriv_one, iteratedDeriv_hPlanar 1 a ha]
    norm_num
  have h0 : hPlanar a = mom a 0 0 := by
    have h := iteratedDeriv_hPlanar 0 a ha
    rw [iteratedDeriv_zero] at h
    simpa using h
  rw [h3, h1, h0]
  linear_combination (-1 : ℂ) * hM33

end Painleve
