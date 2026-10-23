import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Matrix

/-!
# Strict total positivity of the kernel `e^{ξζ}`

For `ξ_1 < ⋯ < ξ_k` and `ζ_1 < ⋯ < ζ_k`, `det[e^{ξ_i ζ_l}] > 0`
(`lem:hankel-signs`). A nonzero sum `∑_l c_l e^{ζ_l ξ}` has at most `k - 1`
real zeros, by induction on `k` with Rolle's theorem applied to
`e^{-ζ_1 ξ} ∑_l c_l e^{ζ_l ξ}`; so the determinant never vanishes on the
convex set of increasing `ζ`. Deforming `ζ` linearly to `(0, 1, …, k-1)`, where
the determinant is a Vandermonde determinant in `e^{ξ_i}`, fixes its sign.
-/

open Set Matrix

namespace Painleve

/-- Zero counting for exponential sums. -/
theorem expSum_eq_zero_of_zeros :
    ∀ (k : ℕ) (ζ : Fin k → ℝ), StrictMono ζ → ∀ (ξ : Fin k → ℝ), StrictMono ξ →
      ∀ c : Fin k → ℝ, (∀ i, ∑ l, c l * Real.exp (ζ l * ξ i) = 0) → c = 0
  | 0, _, _, _, _, c, _ => funext fun i => i.elim0
  | k + 1, ζ, hζ, ξ, hξ, c, hc => by
    -- `g(x) = ∑_l c_l e^{(ζ_l - ζ_0) x}` vanishes at the `k+1` points `ξ_i`
    set g : ℝ → ℝ := fun x => ∑ l, c l * Real.exp ((ζ l - ζ 0) * x) with hg
    set g' : ℝ → ℝ := fun x => ∑ l, c l * ((ζ l - ζ 0) * Real.exp ((ζ l - ζ 0) * x)) with hg'
    have hgz : ∀ i, g (ξ i) = 0 := by
      intro i
      have h := hc i
      have : g (ξ i) = Real.exp (-(ζ 0 * ξ i)) * ∑ l, c l * Real.exp (ζ l * ξ i) := by
        simp only [hg, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show (ζ l - ζ 0) * ξ i = -(ζ 0 * ξ i) + ζ l * ξ i by ring, Real.exp_add]
        ring
      rw [this, h, mul_zero]
    have hderiv : ∀ x, HasDerivAt g (g' x) x := by
      intro x
      have := HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun l x => c l * Real.exp ((ζ l - ζ 0) * x))
        (A' := fun l => c l * ((ζ l - ζ 0) * Real.exp ((ζ l - ζ 0) * x))) (x := x)
        (fun l _ => by
          have h1 := ((hasDerivAt_id x).const_mul (ζ l - ζ 0)).exp
          have h2 := h1.const_mul (c l)
          simp only [id, mul_one] at h2
          exact h2.congr_deriv (by ring))
      simpa [hg, hg'] using this
    have hcont : Continuous g := by rw [hg]; fun_prop
    -- Rolle between consecutive zeros
    have hrolle : ∀ i : Fin k, ∃ η ∈ Ioo (ξ i.castSucc) (ξ i.succ), g' η = 0 := by
      intro i
      have hlt : ξ i.castSucc < ξ i.succ := hξ Fin.castSucc_lt_succ
      exact exists_hasDerivAt_eq_zero hlt hcont.continuousOn
        (by rw [hgz, hgz]) (fun x _ => hderiv x)
    choose η hη hη0 using hrolle
    have hηmono : StrictMono η := by
      intro i j hij
      have hle : i.succ ≤ j.castSucc := by
        rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hij
      calc η i < ξ i.succ := (hη i).2
        _ ≤ ξ j.castSucc := hξ.monotone hle
        _ < η j := (hη j).1
    -- `g'` is an exponential sum with `k` terms and ordered exponents `ζ_{l+1} - ζ_0`
    set ζ' : Fin k → ℝ := fun l => ζ l.succ - ζ 0 with hζ'
    have hζ'mono : StrictMono ζ' := fun l m hlm => by
      simp only [hζ']; linarith [hζ (Fin.succ_lt_succ_iff.mpr hlm)]
    have hζ'pos : ∀ l, 0 < ζ' l := fun l => by
      simp only [hζ']; linarith [hζ (Fin.succ_pos l)]
    have hz' : ∀ i, ∑ l, (c l.succ * ζ' l) * Real.exp (ζ' l * η i) = 0 := by
      intro i
      have h := hη0 i
      simp only [hg'] at h
      rw [Fin.sum_univ_succ] at h
      simp only [sub_self, zero_mul, mul_zero, zero_add] at h
      rw [← h]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hζ']
      ring
    have hih := expSum_eq_zero_of_zeros k ζ' hζ'mono η hηmono _ hz'
    have htail : ∀ l : Fin k, c l.succ = 0 := by
      intro l
      have := congrFun hih l
      simp only [Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact h
      · exact absurd h (hζ'pos l).ne'
    have hhead : c 0 = 0 := by
      have h := hgz 0
      simp only [hg, Fin.sum_univ_succ, sub_self, zero_mul, Real.exp_zero, mul_one, htail,
        zero_mul, Finset.sum_const_zero, add_zero] at h
      exact h
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · exact hhead
    · exact htail l

/-- The kernel matrix `[e^{ξ_i ζ_l}]`. -/
noncomputable def expKer {k : ℕ} (ξ ζ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i l => Real.exp (ξ i * ζ l)

theorem det_expKer_ne_zero {k : ℕ} (ξ ζ : Fin k → ℝ) (hξ : StrictMono ξ) (hζ : StrictMono ζ) :
    (expKer ξ ζ).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hc0
  refine expSum_eq_zero_of_zeros k ζ hζ ξ hξ c fun i => ?_
  have := congrFun hc i
  simp only [Matrix.mulVec, dotProduct, expKer, Matrix.of_apply, Pi.zero_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring_nf

/-- **Strict total positivity of `e^{ξζ}`.** -/
theorem det_expKer_pos {k : ℕ} (ξ ζ : Fin k → ℝ) (hξ : StrictMono ξ) (hζ : StrictMono ζ) :
    0 < (expKer ξ ζ).det := by
  set ι : Fin k → ℝ := fun l => (l : ℕ) with hι
  have hιmono : StrictMono ι := fun l m h => by simp only [hι]; exact_mod_cast h
  set ζs : ℝ → Fin k → ℝ := fun s l => (1 - s) * ζ l + s * ι l with hζs
  have hζsmono : ∀ s ∈ Icc (0 : ℝ) 1, StrictMono (ζs s) := by
    intro s hs l m hlm
    simp only [hζs]
    have h1 := hζ hlm
    have h2 := hιmono hlm
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · subst h0; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact h1
    · nlinarith [hs.2]
  set D : ℝ → ℝ := fun s => (expKer ξ (ζs s)).det with hD
  have hDcont : Continuous D := by
    simp only [hD, expKer, hζs]
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i l => ?_
    simp only [Matrix.of_apply]
    fun_prop
  have hDne : ∀ s ∈ Icc (0 : ℝ) 1, D s ≠ 0 :=
    fun s hs => det_expKer_ne_zero ξ (ζs s) hξ (hζsmono s hs)
  have hD1 : 0 < D 1 := by
    have he : expKer ξ (ζs 1) = Matrix.vandermonde (fun i => Real.exp (ξ i)) := by
      ext i l
      simp only [expKer, hζs, Matrix.of_apply, Matrix.vandermonde_apply, hι, sub_self, zero_mul,
        one_mul, zero_add]
      rw [← Real.exp_nat_mul]; ring_nf
    simp only [hD]
    rw [he, Matrix.det_vandermonde]
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (hξ hij))
  have hD0 : D 0 = (expKer ξ ζ).det := by
    simp only [hD, hζs, sub_zero, one_mul, zero_mul, add_zero]
  rw [← hD0]
  by_contra hneg
  push Not at hneg
  have hlt : D 0 < 0 := lt_of_le_of_ne hneg (hDne 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc (zero_le_one' ℝ) hDcont.continuousOn
    ⟨hlt.le, hD1.le⟩
  exact hDne s hs hs0

end Painleve
