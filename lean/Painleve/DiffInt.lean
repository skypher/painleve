import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Painleve
open MeasureTheory
open scoped ContDiff

/-- The `j`-th derivative of a smooth real-variable function, as a derivative of the
`(j-1)`-st, at every point. -/
theorem hasDerivAt_iteratedDeriv_succ' {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t := by
  have hd : Differentiable ℝ (iteratedDeriv j f) :=
    hf.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)
  rw [iteratedDeriv_succ]
  exact (hd t).hasDerivAt

/-- One differentiation step under the integral sign, on an open set `U`. -/
theorem hasDerivAt_integral_iter {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℝ → α → ℂ) {U : Set ℝ} (hU : IsOpen U)
    (hF : ∀ x, ContDiff ℝ ∞ (fun t => F t x)) (j : ℕ)
    (hm0 : ∀ t, AEStronglyMeasurable (fun x => iteratedDeriv j (fun t => F t x) t) μ)
    (hm1 : ∀ t, AEStronglyMeasurable (fun x => iteratedDeriv (j + 1) (fun t => F t x) t) μ)
    (b0 b1 : α → ℝ) (hi0 : Integrable b0 μ) (hi1 : Integrable b1 μ)
    (hle0 : ∀ t ∈ U, ∀ x, ‖iteratedDeriv j (fun t => F t x) t‖ ≤ b0 x)
    (hle1 : ∀ t ∈ U, ∀ x, ‖iteratedDeriv (j + 1) (fun t => F t x) t‖ ≤ b1 x) :
    ∀ t ∈ U, HasDerivAt (fun s => ∫ x, iteratedDeriv j (fun t => F t x) s ∂μ)
      (∫ x, iteratedDeriv (j + 1) (fun t => F t x) t ∂μ) t := by
  intro t ht
  have hint0 : Integrable (fun x => iteratedDeriv j (fun t => F t x) t) μ :=
    Integrable.mono' hi0 (hm0 t) (ae_of_all μ (fun x => hle0 t ht x))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x => iteratedDeriv j (fun t => F t x) s)
    (F' := fun s x => iteratedDeriv (j + 1) (fun t => F t x) s)
    (x₀ := t) (s := U) (bound := b1) (hU.mem_nhds ht)
    (Filter.Eventually.of_forall hm0) hint0 (hm1 t)
    (ae_of_all μ (fun a x hx => hle1 x hx a)) hi1
    (ae_of_all μ (fun a x _ => hasDerivAt_iteratedDeriv_succ' (hF a) j x))
  exact key.2

/-- Induction on `m`: the `m`-th derivative of the integral is the integral of the
`m`-th derivative, on an open set `U`. -/
theorem iteratedDeriv_integral_aux {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℝ → α → ℂ) {U : Set ℝ} (hU : IsOpen U)
    (hF : ∀ x, ContDiff ℝ ∞ (fun t => F t x)) (bound : ℕ → α → ℝ) (m : ℕ) :
    (∀ j ≤ m, ∀ t, AEStronglyMeasurable (fun x => iteratedDeriv j (fun t => F t x) t) μ) →
    (∀ j ≤ m, Integrable (bound j) μ) →
    (∀ j ≤ m, ∀ t ∈ U, ∀ x, ‖iteratedDeriv j (fun t => F t x) t‖ ≤ bound j x) →
    ∀ t ∈ U, iteratedDeriv m (fun t => ∫ x, F t x ∂μ) t
      = ∫ x, iteratedDeriv m (fun t => F t x) t ∂μ := by
  induction m with
  | zero =>
    intro _ _ _ t _
    simp [iteratedDeriv_zero]
  | succ m ih =>
    intro hmeas hint hle t ht
    have IH := ih (fun j hj => hmeas j (by omega)) (fun j hj => hint j (by omega))
      (fun j hj => hle j (by omega))
    have hev : (iteratedDeriv m (fun t => ∫ x, F t x ∂μ)) =ᶠ[nhds t]
        (fun s => ∫ x, iteratedDeriv m (fun t => F t x) s ∂μ) := by
      filter_upwards [hU.mem_nhds ht] with s hs using IH s hs
    have hL : iteratedDeriv (m + 1) (fun t => ∫ x, F t x ∂μ) t
        = deriv (fun s => ∫ x, iteratedDeriv m (fun t => F t x) s ∂μ) t := by
      rw [iteratedDeriv_succ]
      exact hev.deriv_eq
    rw [hL, (hasDerivAt_integral_iter F hU hF m
      (fun t => hmeas m (by omega) t) (fun t => hmeas (m + 1) (le_refl _) t)
      (bound m) (bound (m + 1)) (hint m (by omega)) (hint (m + 1) (le_refl _))
      (fun t ht x => hle m (by omega) t ht x)
      (fun t ht x => hle (m + 1) (le_refl _) t ht x) t ht).deriv]

/-- Differentiation under the integral sign, `m` times, on the ball `Metric.ball t₀ ε`. -/
theorem iteratedDeriv_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℝ → α → ℂ) {t₀ ε : ℝ} (hε : 0 < ε) (m : ℕ)
    (hF : ∀ x, ContDiff ℝ ∞ (fun t => F t x))
    (hmeas : ∀ j ≤ m, ∀ t, AEStronglyMeasurable (fun x => iteratedDeriv j (fun t => F t x) t) μ)
    (bound : ℕ → α → ℝ)
    (hint : ∀ j ≤ m, Integrable (bound j) μ)
    (hle : ∀ j ≤ m, ∀ t ∈ Metric.ball t₀ ε, ∀ x,
      ‖iteratedDeriv j (fun t => F t x) t‖ ≤ bound j x) :
    ∀ t ∈ Metric.ball t₀ ε,
      iteratedDeriv m (fun t => ∫ x, F t x ∂μ) t = ∫ x, iteratedDeriv m (fun t => F t x) t ∂μ :=
  iteratedDeriv_integral_aux F Metric.isOpen_ball hF bound m hmeas hint hle

end Painleve
