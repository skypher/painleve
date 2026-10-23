import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Order.Field

namespace Painleve
open scoped ContDiff Topology
open Filter

/-- Norm bound on the third derivative from the ODE. -/
lemma norm_iter3_le (W : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hode : iteratedDeriv 3 W s + (s : ℂ) ^ 2 * deriv W s + (s : ℂ) * W s = 0) :
    ‖iteratedDeriv 3 W s‖ ≤ s ^ 2 * ‖deriv W s‖ + s * ‖W s‖ := by
  have e : iteratedDeriv 3 W s = -((s : ℂ) ^ 2 * deriv W s + (s : ℂ) * W s) := by
    linear_combination hode
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]

/-- Real algebra: the energy derivative bound. -/
lemma energy_ineq (s a x0 x1 x2 x3 D : ℝ) (hs : 0 < s) (hsa : s ≤ a)
    (hx2 : 0 ≤ x2) (hx3 : x3 ≤ s ^ 2 * x1 + s * x0)
    (hD : D ≤ 2 * x0 * x1 + 2 * x1 * x2 + 2 * x2 * x3) :
    D ≤ (2 + a ^ 2 + a) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := by
  have h1 : x2 * x3 ≤ x2 * (s ^ 2 * x1 + s * x0) := mul_le_mul_of_nonneg_left hx3 hx2
  have h2 : s ^ 2 + s ≤ a ^ 2 + a := by nlinarith
  have h3 : 2 * x0 * x1 + 2 * x1 * x2 + 2 * x2 * x3 ≤ (2 + s ^ 2 + s) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := by
    nlinarith [sq_nonneg (x0 - x1), sq_nonneg (x1 - x2), mul_nonneg (sq_nonneg s) (sq_nonneg (x1 - x2)),
      mul_nonneg hs.le (sq_nonneg (x0 - x2)), mul_nonneg (sq_nonneg s) (sq_nonneg x0),
      mul_nonneg hs.le (sq_nonneg x1), sq_nonneg x0, sq_nonneg x2]
  have h4 : (2 + s ^ 2 + s) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) ≤ (2 + a ^ 2 + a) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem ode3_unique (W : ℝ → ℂ)
    (hW : ContDiffOn ℝ ∞ W (Set.Ioi 0))
    (hode : ∀ a : ℝ, 0 < a →
      iteratedDeriv 3 W a + (a : ℂ) ^ 2 * deriv W a + (a : ℂ) * W a = 0)
    (h0 : Tendsto W (𝓝[>] 0) (𝓝 0))
    (h1 : Tendsto (deriv W) (𝓝[>] 0) (𝓝 0))
    (h2 : Tendsto (iteratedDeriv 2 W) (𝓝[>] 0) (𝓝 0)) :
    ∀ a : ℝ, 0 < a → W a = 0 := by
  intro a ha
  -- smoothness of the iterated derivatives on (0, ∞)
  have hsm : ∀ j : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv j W) (Set.Ioi 0) := by
    intro j
    induction j with
    | zero => rw [iteratedDeriv_zero]; exact hW
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (le_of_eq rfl)
  have hdiff : ∀ j : ℕ, ∀ s : ℝ, 0 < s →
      HasDerivAt (iteratedDeriv j W) (iteratedDeriv (j + 1) W s) s := by
    intro j s hs
    have hd : DifferentiableAt ℝ (iteratedDeriv j W) s :=
      ((hsm j).differentiableOn (by simp)).differentiableAt
        (Ioi_mem_nhds hs)
    rw [iteratedDeriv_succ]
    exact hd.hasDerivAt
  have hd0 : ∀ s : ℝ, 0 < s → HasDerivAt W (deriv W s) s := by
    intro s hs
    have := hdiff 0 s hs
    rw [iteratedDeriv_zero, zero_add, iteratedDeriv_one] at this
    exact this
  have hd1 : ∀ s : ℝ, 0 < s → HasDerivAt (deriv W) (iteratedDeriv 2 W s) s := by
    intro s hs
    have := hdiff 1 s hs
    rw [iteratedDeriv_one] at this
    exact this
  have hd2 : ∀ s : ℝ, 0 < s → HasDerivAt (iteratedDeriv 2 W) (iteratedDeriv 3 W s) s :=
    fun s hs => hdiff 2 s hs
  -- the energy
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ → ℝ, E = fun t =>
      ‖W t‖ ^ 2 + ‖deriv W t‖ ^ 2 + ‖iteratedDeriv 2 W t‖ ^ 2 := ⟨_, rfl⟩
  have hEt : ∀ t, E t = ‖W t‖ ^ 2 + ‖deriv W t‖ ^ 2 + ‖iteratedDeriv 2 W t‖ ^ 2 :=
    fun t => by rw [hEdef]
  have hEfun : E = fun t => inner ℝ (W t) (W t) + inner ℝ (deriv W t) (deriv W t) +
      inner ℝ (iteratedDeriv 2 W t) (iteratedDeriv 2 W t) := by
    rw [hEdef]
    funext t
    simp only [real_inner_self_eq_norm_sq]
  have hEd : ∀ s : ℝ, 0 < s → HasDerivAt E
      (inner ℝ (W s) (deriv W s) + inner ℝ (deriv W s) (W s) +
        (inner ℝ (deriv W s) (iteratedDeriv 2 W s) + inner ℝ (iteratedDeriv 2 W s) (deriv W s)) +
        (inner ℝ (iteratedDeriv 2 W s) (iteratedDeriv 3 W s) +
          inner ℝ (iteratedDeriv 3 W s) (iteratedDeriv 2 W s))) s := by
    intro s hs
    rw [hEfun]
    exact (((HasDerivAt.inner ℝ (hd0 s hs) (hd0 s hs)).add
      (HasDerivAt.inner ℝ (hd1 s hs) (hd1 s hs)))).add
      (HasDerivAt.inner ℝ (hd2 s hs) (hd2 s hs))
  have hEd2 : ∀ s : ℝ, 0 < s → s ≤ a →
      inner ℝ (W s) (deriv W s) + inner ℝ (deriv W s) (W s) +
        (inner ℝ (deriv W s) (iteratedDeriv 2 W s) + inner ℝ (iteratedDeriv 2 W s) (deriv W s)) +
        (inner ℝ (iteratedDeriv 2 W s) (iteratedDeriv 3 W s) +
          inner ℝ (iteratedDeriv 3 W s) (iteratedDeriv 2 W s)) ≤ (2 + a ^ 2 + a) * E s := by
    intro s hs hsa
    rw [hEt s]
    have i1 := real_inner_le_norm (W s) (deriv W s)
    have i2 := real_inner_le_norm (deriv W s) (W s)
    have i3 := real_inner_le_norm (deriv W s) (iteratedDeriv 2 W s)
    have i4 := real_inner_le_norm (iteratedDeriv 2 W s) (deriv W s)
    have i5 := real_inner_le_norm (iteratedDeriv 2 W s) (iteratedDeriv 3 W s)
    have i6 := real_inner_le_norm (iteratedDeriv 3 W s) (iteratedDeriv 2 W s)
    have hx3 := norm_iter3_le W s hs (hode s hs)
    have hD : inner ℝ (W s) (deriv W s) + inner ℝ (deriv W s) (W s) +
        (inner ℝ (deriv W s) (iteratedDeriv 2 W s) + inner ℝ (iteratedDeriv 2 W s) (deriv W s)) +
        (inner ℝ (iteratedDeriv 2 W s) (iteratedDeriv 3 W s) +
          inner ℝ (iteratedDeriv 3 W s) (iteratedDeriv 2 W s)) ≤
        2 * ‖W s‖ * ‖deriv W s‖ + 2 * ‖deriv W s‖ * ‖iteratedDeriv 2 W s‖ +
          2 * ‖iteratedDeriv 2 W s‖ * ‖iteratedDeriv 3 W s‖ := by
      linarith
    exact energy_ineq s a _ _ _ _ _ hs hsa (norm_nonneg _) hx3 hD
  -- the monotone quantity F(s) = E(s) exp(-K s)
  have hFHas : ∀ x : ℝ, 0 < x → x ≤ a → ∃ f' : ℝ,
      HasDerivAt (fun t => E t * Real.exp (-((2 + a ^ 2 + a) * t))) f' x ∧ f' ≤ 0 := by
    intro x hx hxa
    have hexp : HasDerivAt (fun t => Real.exp (-((2 + a ^ 2 + a) * t)))
        (Real.exp (-((2 + a ^ 2 + a) * x)) * (-(2 + a ^ 2 + a))) x := by
      have := (((hasDerivAt_id x).const_mul (2 + a ^ 2 + a)).neg).exp
      exact this.congr_deriv (by simp)
    have hF := (hEd x hx).mul hexp
    refine ⟨_, hF, ?_⟩
    have hle := mul_le_mul_of_nonneg_right (hEd2 x hx hxa) (Real.exp_pos (-((2 + a ^ 2 + a) * x))).le
    linarith
  -- F is antitone on (0, a]
  have hanti : AntitoneOn (fun t => E t * Real.exp (-((2 + a ^ 2 + a) * t))) (Set.Ioc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 a)
    · intro x hx
      obtain ⟨f', hf', -⟩ := hFHas x hx.1 hx.2
      exact hf'.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      obtain ⟨f', hf', -⟩ := hFHas x hx.1 hx.2.le
      exact hf'.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      obtain ⟨f', hf', hle⟩ := hFHas x hx.1 hx.2.le
      rw [hf'.deriv]
      exact hle
  -- the limit of F at 0⁺ is 0
  have hE0 : Tendsto E (𝓝[>] 0) (𝓝 0) := by
    have hfun : E = fun t => ‖W t‖ ^ 2 + ‖deriv W t‖ ^ 2 + ‖iteratedDeriv 2 W t‖ ^ 2 :=
      funext hEt
    rw [hfun]
    have h := ((h0.norm.pow 2).add (h1.norm.pow 2)).add (h2.norm.pow 2)
    simpa using h
  have hexpT : Tendsto (fun t : ℝ => Real.exp (-((2 + a ^ 2 + a) * t))) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-((2 + a ^ 2 + a) * t))) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have hLim : Tendsto (fun t => E t * Real.exp (-((2 + a ^ 2 + a) * t))) (𝓝[>] 0) (𝓝 0) := by
    have := hE0.mul hexpT
    simpa using this
  have hFa : E a * Real.exp (-((2 + a ^ 2 + a) * a)) ≤ 0 := by
    apply ge_of_tendsto hLim
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    exact hanti ⟨hε.1, hε.2.le⟩ ⟨ha, le_rfl⟩ hε.2.le
  have hEa : E a ≤ 0 := by
    by_contra hc
    have := mul_pos (not_le.mp hc) (Real.exp_pos (-((2 + a ^ 2 + a) * a)))
    linarith
  have hnorm : ‖W a‖ ^ 2 ≤ 0 := by
    rw [hEt a] at hEa
    nlinarith [sq_nonneg ‖deriv W a‖, sq_nonneg ‖iteratedDeriv 2 W a‖]
  have hz : ‖W a‖ = 0 := by
    nlinarith [norm_nonneg (W a)]
  exact norm_eq_zero.mp hz

end Painleve
