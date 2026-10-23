import Painleve.ConvSmooth

/-!
# Differentiating `∫ g(w) q_β(w - u) dw` on the kernel

For bounded continuous `g`,
`∂_u^j ∫ g(w) q_β(w-u) dw = ∫ g(w) (-1)^j q_β^{(j)}(w-u) dw`, where
`q_β^{(j)}(v) = q_β(v) P_j(e^v)` (`lem:hankel-signs`, final step: "On `|u| ≤ M`,
`|q_m^{(q)}(w-u)| ≤ C e^{β_m w}(1+e^w)^q exp(-e^{-M} e^w)`, which is integrable").
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace Painleve

lemma qLog_eq_expKerFn (β : ℝ) : qLog β = fun v => expKerFn β 1 v / Real.Gamma β := by
  funext v; unfold qLog expKerFn; ring_nf

lemma iteratedDeriv_qLog (β : ℝ) (j : ℕ) :
    iteratedDeriv j (qLog β)
      = fun v => expKerFn β 1 v * (derPoly β 1 j).eval (Real.exp v) / Real.Gamma β := by
  rw [qLog_eq_expKerFn]
  have : (fun v => expKerFn β 1 v / Real.Gamma β) = fun v => (Real.Gamma β)⁻¹ * expKerFn β 1 v := by
    funext v; ring
  rw [this]
  funext v
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_expKerFn]
  ring

lemma contDiff_qLog (β : ℝ) : ContDiff ℝ ∞ (qLog β) := by
  rw [qLog_eq_expKerFn]
  exact ((contDiff_expKerFn β 1).of_le le_top).div_const _

/-- `v ↦ exp(βv - c e^v)` is integrable for `β, c > 0`. -/
lemma integrable_exp_lin_sub_exp {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Integrable (fun v : ℝ => Real.exp (β * v - c * Real.exp v)) := by
  have h := ((integrable_qLog hβ).comp_add_right (Real.log c)).const_mul
    (Real.Gamma β * Real.exp (-(β * Real.log c)))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [qLog]
  have hG : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
  rw [Real.exp_add, Real.exp_log hc]
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

/-- A locally uniform integrable bound for the kernel derivatives. -/
lemma kernel_bound {β : ℝ} (hβ : 0 < β) (j : ℕ) (u₀ : ℝ) :
    ∃ B : ℝ → ℝ, Integrable B ∧
      ∀ u ∈ ball u₀ 1, ∀ w, |iteratedDeriv j (qLog β) (w - u)| ≤ B w := by
  obtain ⟨C, hC⟩ := bdd_poly_mul_exp (derPoly β 1 j) (c := 1 / 2) (by norm_num)
  have hG : 0 < Real.Gamma β := Real.Gamma_pos_of_pos hβ
  set c : ℝ := Real.exp (-1) / 2 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨fun w => C / Real.Gamma β * Real.exp β *
      Real.exp (β * (w - u₀) - c * Real.exp (w - u₀)), ?_, fun u hu w => ?_⟩
  · exact ((integrable_exp_lin_sub_exp hβ hcpos).comp_sub_right u₀).const_mul _
  · rw [iteratedDeriv_qLog]
    simp only
    have hu' : |u - u₀| < 1 := by rw [← Real.dist_eq]; exact hu
    have h1 := hC (Real.exp (w - u)) (Real.exp_pos _).le
    have hsplit : expKerFn β 1 (w - u) * (derPoly β 1 j).eval (Real.exp (w - u))
        = Real.exp (β * (w - u) - Real.exp (w - u) / 2) *
          ((derPoly β 1 j).eval (Real.exp (w - u)) * Real.exp (-(1 / 2) * Real.exp (w - u))) := by
      unfold expKerFn
      rw [mul_comm ((derPoly β 1 j).eval _), ← mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [hsplit, abs_div, abs_of_pos hG, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (β * (w - u) - Real.exp (w - u) / 2)
        ≤ Real.exp β * Real.exp (β * (w - u₀) - c * Real.exp (w - u₀)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hb : β * (w - u) ≤ β + β * (w - u₀) := by
        have : u₀ - u < 1 := by linarith [(abs_lt.mp hu').1]
        nlinarith
      have he : c * Real.exp (w - u₀) ≤ Real.exp (w - u) / 2 := by
        have : Real.exp (-1) * Real.exp (w - u₀) ≤ Real.exp (w - u) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith [(abs_lt.mp hu').2])
        rw [hc]; linarith
      linarith
    calc Real.exp (β * (w - u) - Real.exp (w - u) / 2) *
          |(derPoly β 1 j).eval (Real.exp (w - u)) * Real.exp (-(1 / 2) * Real.exp (w - u))|
          / Real.Gamma β
        ≤ (Real.exp β * Real.exp (β * (w - u₀) - c * Real.exp (w - u₀))) * C / Real.Gamma β := by
          refine div_le_div_of_nonneg_right ?_ hG.le
          exact mul_le_mul hexp h1 (abs_nonneg _) (by positivity)
      _ = C / Real.Gamma β * Real.exp β *
            Real.exp (β * (w - u₀) - c * Real.exp (w - u₀)) := by ring

/-- `convT` in kernel form: `∫ q_β(x) g(u+x) dx = ∫ g(w) q_β(w-u) dw`. -/
lemma convT_eq_kernel (β : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    convT β g u = ∫ w, g w * qLog β (w - u) := by
  unfold convT
  have := integral_add_left_eq_self (μ := volume) (fun w => g w * qLog β (w - u)) u
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_left]
  ring

lemma hasDerivAt_kernel_shift (β : ℝ) (j : ℕ) (w u : ℝ) :
    HasDerivAt (fun u => iteratedDeriv j (qLog β) (w - u))
      (-iteratedDeriv (j + 1) (qLog β) (w - u)) u := by
  have hd : HasDerivAt (iteratedDeriv j (qLog β)) (iteratedDeriv (j + 1) (qLog β) (w - u))
      (w - u) := by
    rw [iteratedDeriv_succ]
    exact ((contDiff_qLog β).differentiable_iteratedDeriv j
      (by exact_mod_cast WithTop.coe_lt_top _) (w - u)).hasDerivAt
  have := hd.comp u ((hasDerivAt_id u).const_sub w)
  exact this.congr_deriv (by simp)

/-- **Derivatives on the kernel.** -/
theorem iteratedDeriv_convT_kernel {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) (j : ℕ) :
    iteratedDeriv j (convT β g)
      = fun u => ∫ w, g w * ((-1) ^ j * iteratedDeriv j (qLog β) (w - u)) := by
  induction j with
  | zero =>
    funext u
    rw [iteratedDeriv_zero, convT_eq_kernel]
    simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext u₀
    obtain ⟨B0, hB0i, hB0⟩ := kernel_bound hβ j u₀
    obtain ⟨B1, hB1i, hB1⟩ := kernel_bound hβ (j + 1) u₀
    have hmeas : ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun w => g w * ((-1) ^ m * iteratedDeriv m (qLog β) (w - u))) volume := by
      intro m u
      refine (hg.mul (continuous_const.mul ?_)).aestronglyMeasurable
      exact ((contDiff_qLog β).continuous_iteratedDeriv m
        (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)).comp (continuous_id.sub continuous_const)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hint0 : Integrable (fun w => g w * ((-1) ^ j * iteratedDeriv j (qLog β) (w - u₀))) := by
      refine Integrable.mono' (hB0i.const_mul C) (hmeas j u₀) (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul (hC w) (hB0 u₀ (mem_ball_self one_pos) w) (abs_nonneg _) hC0
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun u w => g w * ((-1) ^ j * iteratedDeriv j (qLog β) (w - u)))
      (F' := fun u w => g w * ((-1) ^ (j + 1) * iteratedDeriv (j + 1) (qLog β) (w - u)))
      (x₀ := u₀) (s := ball u₀ 1) (bound := fun w => C * B1 w) (ball_mem_nhds u₀ one_pos)
      (Eventually.of_forall fun u => hmeas j u) hint0 (hmeas (j + 1) u₀)
      (Eventually.of_forall fun w u hu => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact mul_le_mul (hC w) (hB1 u hu w) (abs_nonneg _) hC0)
      (hB1i.const_mul C)
      (Eventually.of_forall fun w u _ => by
        have := (hasDerivAt_kernel_shift β j w u).const_mul ((-1 : ℝ) ^ j) |>.const_mul (g w)
        refine this.congr_deriv ?_
        rw [pow_succ]; ring)
    exact key.2.deriv

end Painleve
