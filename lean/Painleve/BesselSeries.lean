import Painleve.Statement
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open scoped ContDiff

namespace Painleve

noncomputable def besselS (ν x : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k / ((4 : ℝ) ^ k * (k.factorial : ℝ) * Real.Gamma (k + ν + 1)) * x ^ (2 * k)

/-- Coefficients of the even series. -/
noncomputable def gc (ν : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k / ((4 : ℝ) ^ k * (k.factorial : ℝ) * Real.Gamma (k + ν + 1))

/-- Ordinary power series `∑ c_k y^k`. -/
noncomputable def pser (c : ℕ → ℝ) (y : ℝ) : ℝ := ∑' k : ℕ, c k * y ^ k

/-- Coefficient sequence `(k+1) c_{k+1}` of the derivative. -/
noncomputable def dseq (c : ℕ → ℝ) : ℕ → ℝ := fun k => ((k : ℝ) + 1) * c (k + 1)

/-- Shift `d ↦ (0, d_0, d_1, …)`. -/
noncomputable def shf (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => d k

/-- Coefficients dominated by `K r^k / k!`. -/
abbrev Bd (c : ℕ → ℝ) : Prop :=
  ∃ K r : ℝ, 0 ≤ K ∧ 0 ≤ r ∧ ∀ k : ℕ, |c k| ≤ K * r ^ k / (k.factorial : ℝ)

theorem summable_bd {c : ℕ → ℝ} (hc : Bd c) (y : ℝ) : Summable (fun k : ℕ => c k * y ^ k) := by
  obtain ⟨K, r, hK, hr, hb⟩ := hc
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (r * |y|)).mul_left K) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |c k| * |y| ^ k ≤ (K * r ^ k / (k.factorial : ℝ)) * |y| ^ k :=
        mul_le_mul_of_nonneg_right (hb k) (by positivity)
    _ = K * ((r * |y|) ^ k / (k.factorial : ℝ)) := by rw [mul_pow]; ring

theorem bd_dseq {c : ℕ → ℝ} (hc : Bd c) : Bd (dseq c) := by
  obtain ⟨K, r, hK, hr, hb⟩ := hc
  refine ⟨K * r, r, mul_nonneg hK hr, hr, fun k => ?_⟩
  unfold dseq
  have hf : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  calc ((k : ℝ) + 1) * |c (k + 1)| ≤ ((k : ℝ) + 1) * (K * r ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb (k + 1)) (by positivity)
    _ = K * r * r ^ k / (k.factorial : ℝ) := by
        rw [hf, pow_succ]
        field_simp

theorem nat_mul_pow_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    (n : ℝ) * R ^ (n - 1) ≤ 2 ^ n * (R + 1) ^ n := by
  rcases n with _ | m
  · simp
  · have h1 : ((m + 1 : ℕ) : ℝ) ≤ 2 ^ (m + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self : m + 1 < 2 ^ (m + 1)).le
    have h2 : R ^ m ≤ (R + 1) ^ (m + 1) :=
      (pow_le_pow_left₀ hR (by linarith) m).trans (pow_le_pow_right₀ (by linarith) (by omega))
    have h3 : m + 1 - 1 = m := by omega
    rw [h3]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem deriv_term_le {c : ℕ → ℝ} {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hb : ∀ k : ℕ, |c k| ≤ K * r ^ k / (k.factorial : ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (z : ℝ) (hz : |z| ≤ R) :
    ‖c n * ((n : ℝ) * z ^ (n - 1))‖ ≤ K * ((2 * r * (R + 1)) ^ n / (n.factorial : ℝ)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), abs_pow]
  have hA : |c n| * ((n : ℝ) * |z| ^ (n - 1))
      ≤ (K * r ^ n / (n.factorial : ℝ)) * (2 ^ n * (R + 1) ^ n) := by
    refine mul_le_mul (hb n) ?_ (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hz (n - 1))
      (Nat.cast_nonneg (α := ℝ) n)).trans (nat_mul_pow_le R hR n)
  refine hA.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow]
  ring

theorem hasDerivAt_pser {c : ℕ → ℝ} (hc : Bd c) (y : ℝ) :
    HasDerivAt (pser c) (pser (dseq c) y) y := by
  obtain ⟨K, r, hK, hr, hb⟩ := hc
  have hc' : Bd c := ⟨K, r, hK, hr, hb⟩
  set R : ℝ := |y| + 1 with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hyR : y ∈ Metric.ball (0 : ℝ) R := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs, hRdef]
    linarith [le_abs_self y, abs_nonneg y]
  have hu : Summable (fun n : ℕ => K * ((2 * r * (R + 1)) ^ n / (n.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial (2 * r * (R + 1))).mul_left K
  have hbound : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℝ) R,
      ‖c n * ((n : ℝ) * z ^ (n - 1))‖ ≤ K * ((2 * r * (R + 1)) ^ n / (n.factorial : ℝ)) := by
    intro n z hz
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz
    exact deriv_term_le hK hr hb R hR n z hz.le
  have hsum : Summable (fun n : ℕ => c n * ((n : ℝ) * y ^ (n - 1))) :=
    Summable.of_norm_bounded hu (fun n => hbound n y hyR)
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun n (z : ℝ) => c n * z ^ n)
    (g' := fun n (z : ℝ) => c n * ((n : ℝ) * z ^ (n - 1)))
    (u := fun n => K * ((2 * r * (R + 1)) ^ n / (n.factorial : ℝ)))
    (y₀ := 0) hu Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected
    (fun n z _ => (hasDerivAt_pow n z).const_mul (c n)) hbound
    (Metric.mem_ball_self hRpos) (summable_bd hc' 0) hyR
  have key : ∑' n : ℕ, c n * ((n : ℝ) * y ^ (n - 1)) = pser (dseq c) y := by
    rw [hsum.tsum_eq_zero_add]
    unfold pser dseq
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    refine tsum_congr fun k => ?_
    push_cast
    ring
  rw [← key]
  exact hd

theorem gamma_lower (ν : ℝ) (hν : -1 < ν) (k : ℕ) :
    (1 + ν) ^ k * Real.Gamma (ν + 1) ≤ Real.Gamma (k + ν + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hs : (0 : ℝ) < (k : ℝ) + ν + 1 := by linarith
    have hg : Real.Gamma (((k + 1 : ℕ) : ℝ) + ν + 1) = ((k : ℝ) + ν + 1) * Real.Gamma ((k : ℝ) + ν + 1) := by
      rw [show ((k + 1 : ℕ) : ℝ) + ν + 1 = ((k : ℝ) + ν + 1) + 1 by push_cast; ring]
      exact Real.Gamma_add_one hs.ne'
    have hpos : 0 < Real.Gamma ((k : ℝ) + ν + 1) := Real.Gamma_pos_of_pos hs
    have h1 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + ν)
    have h2 : (1 + ν) * Real.Gamma ((k : ℝ) + ν + 1) ≤ ((k : ℝ) + ν + 1) * Real.Gamma ((k : ℝ) + ν + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    rw [hg, pow_succ]
    nlinarith [h1, h2]

theorem bd_gc (ν : ℝ) (hν : -1 < ν) : Bd (gc ν) := by
  have hG : 0 < Real.Gamma (ν + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h1ν : 0 < 1 + ν := by linarith
  refine ⟨1 / Real.Gamma (ν + 1), 1 / (4 * (1 + ν)), by positivity, by positivity, fun k => ?_⟩
  unfold gc
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hGk : 0 < Real.Gamma ((k : ℝ) + ν + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hL := gamma_lower ν hν k
  have hden : (0 : ℝ) < (4 : ℝ) ^ k * (k.factorial : ℝ) * Real.Gamma ((k : ℝ) + ν + 1) :=
    mul_pos (mul_pos (by positivity) hk) hGk
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hden]
  have hRHS : 1 / Real.Gamma (ν + 1) * (1 / (4 * (1 + ν))) ^ k / (k.factorial : ℝ)
      = 1 / (Real.Gamma (ν + 1) * (4 * (1 + ν)) ^ k * (k.factorial : ℝ)) := by
    rw [div_pow, one_pow]
    field_simp
  rw [hRHS]
  apply one_div_le_one_div_of_le
  · positivity
  · have e : Real.Gamma (ν + 1) * (4 * (1 + ν)) ^ k * (k.factorial : ℝ)
        = (4 : ℝ) ^ k * (k.factorial : ℝ) * ((1 + ν) ^ k * Real.Gamma (ν + 1)) := by
      rw [mul_pow]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hL (by positivity)

theorem gc_rec (ν : ℝ) (hν : -1 < ν) (k : ℕ) :
    4 * ((k : ℝ) + 1) * ((k : ℝ) + ν + 1) * gc ν (k + 1) + gc ν k = 0 := by
  unfold gc
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : (0 : ℝ) < (k : ℝ) + ν + 1 := by linarith
  have hG : 0 < Real.Gamma ((k : ℝ) + ν + 1) := Real.Gamma_pos_of_pos hs
  have hg : Real.Gamma (((k + 1 : ℕ) : ℝ) + ν + 1) = ((k : ℝ) + ν + 1) * Real.Gamma ((k : ℝ) + ν + 1) := by
    rw [show ((k + 1 : ℕ) : ℝ) + ν + 1 = ((k : ℝ) + ν + 1) + 1 by push_cast; ring]
    exact Real.Gamma_add_one hs.ne'
  rw [hg, Nat.factorial_succ]
  push_cast
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Termwise identity for the ODE of the power series. -/
theorem shf_dseq_zero_sum (ν : ℝ) (hν : -1 < ν) (k : ℕ) :
    4 * shf (dseq (dseq (gc ν))) k + 4 * (ν + 1) * dseq (gc ν) k + gc ν k = 0 := by
  cases k with
  | zero =>
    have h0 := gc_rec ν hν 0
    simp only [shf, dseq]
    push_cast at h0 ⊢
    linear_combination h0
  | succ j =>
    have h0 := gc_rec ν hν (j + 1)
    simp only [shf, dseq]
    push_cast at h0 ⊢
    linear_combination h0

theorem summable_shf {d : ℕ → ℝ} (hd : Bd d) (y : ℝ) :
    Summable (fun k : ℕ => shf d k * y ^ k) := by
  refine (summable_nat_add_iff 1).mp ?_
  have e : (fun n : ℕ => shf d (n + 1) * y ^ (n + 1)) = fun n => y * (d n * y ^ n) := by
    funext n
    rw [show shf d (n + 1) = d n from rfl]
    ring
  show Summable (fun n : ℕ => shf d (n + 1) * y ^ (n + 1))
  rw [e]
  exact (summable_bd hd y).mul_left y

theorem mul_pser_eq_shf {d : ℕ → ℝ} (hd : Bd d) (y : ℝ) :
    y * pser d y = ∑' k : ℕ, shf d k * y ^ k := by
  have hs := summable_shf hd y
  rw [hs.tsum_eq_zero_add]
  unfold pser
  simp only [shf, pow_zero, mul_one, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

theorem pser_ode (ν : ℝ) (hν : -1 < ν) (y : ℝ) :
    4 * y * pser (dseq (dseq (gc ν))) y + 4 * (ν + 1) * pser (dseq (gc ν)) y
      + pser (gc ν) y = 0 := by
  have hc : Bd (gc ν) := bd_gc ν hν
  have hD : Bd (dseq (gc ν)) := bd_dseq hc
  have hDD : Bd (dseq (dseq (gc ν))) := bd_dseq hD
  have hA := summable_shf hDD y
  have hB := summable_bd hD y
  have hC := summable_bd hc y
  rw [mul_assoc, mul_pser_eq_shf hDD y]
  unfold pser
  have hz : ∀ k : ℕ, 4 * (shf (dseq (dseq (gc ν))) k * y ^ k)
      + 4 * (ν + 1) * (dseq (gc ν) k * y ^ k) + gc ν k * y ^ k = 0 := fun k => by
    linear_combination (y ^ k) * shf_dseq_zero_sum ν hν k
  have hA4 : Summable (fun k : ℕ => 4 * (shf (dseq (dseq (gc ν))) k * y ^ k)) := hA.mul_left 4
  have hB4 : Summable (fun k : ℕ => 4 * (ν + 1) * (dseq (gc ν) k * y ^ k)) := hB.mul_left _
  have hzero : ∑' k : ℕ, (4 * (shf (dseq (dseq (gc ν))) k * y ^ k)
      + 4 * (ν + 1) * (dseq (gc ν) k * y ^ k) + gc ν k * y ^ k) = 0 := by
    simp only [hz, tsum_zero]
  rw [Summable.tsum_add (hA4.add hB4) hC, Summable.tsum_add hA4 hB4, tsum_mul_left,
    tsum_mul_left] at hzero
  linarith [hzero]

theorem differentiable_iter (m : ℕ) :
    ∀ c : ℕ → ℝ, Bd c → Differentiable ℝ (iteratedDeriv m (pser c)) := by
  induction m with
  | zero =>
    intro c hc
    rw [iteratedDeriv_zero]
    exact fun y => (hasDerivAt_pser hc y).differentiableAt
  | succ m ih =>
    intro c hc
    rw [iteratedDeriv_succ']
    have hfun : deriv (pser c) = pser (dseq c) := funext fun y => (hasDerivAt_pser hc y).deriv
    rw [hfun]
    exact ih (dseq c) (bd_dseq hc)

theorem besselS_eq (ν : ℝ) : besselS ν = fun x => pser (gc ν) (x ^ 2) := by
  funext x
  unfold besselS pser gc
  refine tsum_congr fun k => ?_
  rw [pow_mul]

theorem besselS_contDiff (ν : ℝ) (hν : -1 < ν) : ContDiff ℝ ∞ (besselS ν) := by
  have hG : ContDiff ℝ ∞ (pser (gc ν)) :=
    contDiff_of_differentiable_iteratedDeriv fun m _ => differentiable_iter m _ (bd_gc ν hν)
  rw [besselS_eq]
  exact hG.comp (contDiff_id.pow 2)

theorem besselS_zero (ν : ℝ) (hν : -1 < ν) : besselS ν 0 = 1 / Real.Gamma (ν + 1) := by
  unfold besselS
  rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow (show 2 * k ≠ 0 by omega), mul_zero])]
  simp

theorem besselJ_eq (ν x : ℝ) (hν : -1 < ν) (hx : 0 < x) :
    besselJ ν x = (x / 2) ^ ν * besselS ν x := by
  unfold besselJ besselS
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h2 : (0 : ℝ) < x / 2 := by positivity
  have h3 : (x / 2) ^ (2 * (k : ℝ)) = x ^ (2 * k) / 4 ^ k := by
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, div_pow,
      show (2 : ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
  have hpow : (x / 2) ^ (2 * (k : ℝ) + ν) = x ^ (2 * k) / 4 ^ k * (x / 2) ^ ν := by
    rw [Real.rpow_add h2, h3]
  rw [hpow]
  ring

theorem besselS_hasDerivAt (ν : ℝ) (hν : -1 < ν) (x : ℝ) :
    HasDerivAt (besselS ν) (pser (dseq (gc ν)) (x ^ 2) * (2 * x)) x := by
  rw [besselS_eq]
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  exact (hasDerivAt_pser (bd_gc ν hν) (x ^ 2)).comp x h2

theorem deriv_besselS_zero (ν : ℝ) (hν : -1 < ν) : deriv (besselS ν) 0 = 0 := by
  rw [(besselS_hasDerivAt ν hν 0).deriv]
  simp

theorem besselS_ode (ν : ℝ) (hν : -1 < ν) (x : ℝ) :
    x * iteratedDeriv 2 (besselS ν) x + (2 * ν + 1) * deriv (besselS ν) x + x * besselS ν x = 0 := by
  have hD : Bd (dseq (gc ν)) := bd_dseq (bd_gc ν hν)
  have hd1 : deriv (besselS ν) = fun x => pser (dseq (gc ν)) (x ^ 2) * (2 * x) :=
    funext fun x => (besselS_hasDerivAt ν hν x).deriv
  have hd2 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => pser (dseq (gc ν)) (x ^ 2) * (2 * x))
      (pser (dseq (dseq (gc ν))) (x ^ 2) * (2 * x) * (2 * x)
        + pser (dseq (gc ν)) (x ^ 2) * 2) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h1 := (hasDerivAt_pser hD (x ^ 2)).comp x h2
    have h3 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    exact h1.mul h3
  have h2nd : iteratedDeriv 2 (besselS ν) = fun x => pser (dseq (dseq (gc ν))) (x ^ 2) * (2 * x) * (2 * x)
      + pser (dseq (gc ν)) (x ^ 2) * 2 := by
    have e : iteratedDeriv 2 (besselS ν) = deriv (iteratedDeriv 1 (besselS ν)) :=
      iteratedDeriv_succ (n := 1) (f := besselS ν)
    rw [e, iteratedDeriv_one, hd1]
    funext x
    exact (hd2 x).deriv
  rw [h2nd, hd1, besselS_eq]
  have hode := pser_ode ν hν (x ^ 2)
  beta_reduce
  linear_combination x * hode

end Painleve
