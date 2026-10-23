import Painleve.LogGamma
import Painleve.PolyDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Convolution with a log-Gamma density preserves bounded smoothness

`(T_β f)(u) = ∫ q_β(x) f(u + x) dx = E[f(u + log G)]`, `G ~ Gamma(β)`. If `f` is
smooth with bounded derivatives of every order, so is `T_β f`, and
`(T_β f)^{(n)} = T_β (f^{(n)})` (`lem:hankel-signs`: "by induction and dominated
convergence, each `φ_j` is smooth with bounded derivatives").
-/

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Painleve

/-- `(T_β f)(u) = ∫ q_β(x) f(u + x) dx`. -/
noncomputable def convT (β : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := ∫ x, qLog β x * f (u + x)

/-- Smooth, with every derivative bounded. -/
def SmoothBdd (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C, ∀ x, |iteratedDeriv n f x| ≤ C

lemma integrable_qLog_mul {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (u : ℝ) : Integrable (fun x => qLog β x * g (u + x)) := by
  refine Integrable.mono' ((integrable_qLog hβ).const_mul C) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((measurable_qLog β).aestronglyMeasurable).mul
      ((hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (qLog_nonneg hβ x), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (qLog_nonneg hβ x)

lemma abs_convT_le {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (u : ℝ) : |convT β g u| ≤ C := by
  unfold convT
  have h := norm_integral_le_of_norm_le ((integrable_qLog hβ).const_mul C)
    (Eventually.of_forall fun x => by
      show ‖qLog β x * g (u + x)‖ ≤ C * qLog β x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (qLog_nonneg hβ x), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (qLog_nonneg hβ x))
  rw [integral_const_mul, integral_qLog hβ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- One differentiation under the integral sign. -/
lemma hasDerivAt_convT {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hgd : Differentiable ℝ g)
    (hgc : Continuous g) (hg'c : Continuous (deriv g)) {C0 C1 : ℝ}
    (h0 : ∀ x, |g x| ≤ C0) (h1 : ∀ x, |deriv g x| ≤ C1) (u : ℝ) :
    HasDerivAt (convT β g) (convT β (deriv g) u) u := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun u x => qLog β x * g (u + x)) (F' := fun u x => qLog β x * deriv g (u + x))
    (x₀ := u) (s := univ) (bound := fun x => C1 * qLog β x) univ_mem
    (Eventually.of_forall fun v => (integrable_qLog_mul hβ hgc h0 v).aestronglyMeasurable)
    (integrable_qLog_mul hβ hgc h0 u)
    (integrable_qLog_mul hβ hg'c h1 u).aestronglyMeasurable
    (Eventually.of_forall fun x v _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (qLog_nonneg hβ x), mul_comm C1]
      exact mul_le_mul_of_nonneg_left (h1 _) (qLog_nonneg hβ x))
    ((integrable_qLog hβ).const_mul C1)
    (Eventually.of_forall fun x v _ => by
      have := ((hgd (v + x)).hasDerivAt).comp v ((hasDerivAt_id v).add_const x)
      simp only [id, mul_one] at this
      exact this.const_mul (qLog β x))
  exact key.2

lemma SmoothBdd.continuous_iteratedDeriv {f : ℝ → ℝ} (hf : SmoothBdd f) (n : ℕ) :
    Continuous (iteratedDeriv n f) :=
  hf.1.continuous_iteratedDeriv n (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)

lemma SmoothBdd.differentiable_iteratedDeriv {f : ℝ → ℝ} (hf : SmoothBdd f) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n f) :=
  hf.1.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)

theorem iteratedDeriv_convT {β : ℝ} (hβ : 0 < β) {f : ℝ → ℝ} (hf : SmoothBdd f) (n : ℕ) :
    iteratedDeriv n (convT β f) = convT β (iteratedDeriv n f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext u
    obtain ⟨C0, hC0⟩ := hf.2 n
    obtain ⟨C1, hC1⟩ := hf.2 (n + 1)
    have hd : deriv (iteratedDeriv n f) = iteratedDeriv (n + 1) f := (iteratedDeriv_succ).symm
    refine (hasDerivAt_convT hβ (hf.differentiable_iteratedDeriv n)
      (hf.continuous_iteratedDeriv n) (by rw [hd]; exact hf.continuous_iteratedDeriv (n + 1))
      hC0 (by rw [hd]; exact hC1) u).deriv

theorem SmoothBdd.convT {β : ℝ} (hβ : 0 < β) {f : ℝ → ℝ} (hf : SmoothBdd f) :
    SmoothBdd (convT β f) := by
  refine ⟨?_, fun n => ?_⟩
  · refine contDiff_of_differentiable_iteratedDeriv (n := ⊤) fun m _ => ?_
    rw [iteratedDeriv_convT hβ hf m]
    intro u
    obtain ⟨C0, hC0⟩ := hf.2 m
    obtain ⟨C1, hC1⟩ := hf.2 (m + 1)
    have hd : deriv (iteratedDeriv m f) = iteratedDeriv (m + 1) f := (iteratedDeriv_succ).symm
    exact (hasDerivAt_convT hβ (hf.differentiable_iteratedDeriv m)
      (hf.continuous_iteratedDeriv m) (by rw [hd]; exact hf.continuous_iteratedDeriv (m + 1))
      hC0 (by rw [hd]; exact hC1) u).differentiableAt
  · obtain ⟨C, hC⟩ := hf.2 n
    refine ⟨C, fun u => ?_⟩
    rw [iteratedDeriv_convT hβ hf n]
    exact abs_convT_le hβ (hf.continuous_iteratedDeriv n) hC u

/-- The base kernel `φ_0(u) = exp(-e^u)`. -/
theorem smoothBdd_base : SmoothBdd (expKerFn 0 1) := by
  refine ⟨(contDiff_expKerFn 0 1).of_le le_top, fun n => ?_⟩
  obtain ⟨C, hC⟩ := bdd_poly_mul_exp (derPoly 0 1 n) one_pos
  refine ⟨C, fun u => ?_⟩
  rw [iteratedDeriv_expKerFn]
  have := hC (Real.exp u) (Real.exp_pos u).le
  unfold expKerFn
  simp only
  rw [show (0 : ℝ) * u - 1 * Real.exp u = -1 * Real.exp u by ring, mul_comm]
  exact this

end Painleve
