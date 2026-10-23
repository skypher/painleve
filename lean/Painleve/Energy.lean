import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Finset Filter Topology

namespace Painleve

/-- Quadratic identity `(Σ z)(Σ h² z) = (Σ h z)² + Σ_{r<s} (h_r−h_s)² z_r z_s`. -/
lemma quad_identity (h0 h1 h2 z0 z1 z2 : ℝ) :
    (z0 + z1 + z2) * (h0 ^ 2 * z0 + h1 ^ 2 * z1 + h2 ^ 2 * z2)
      = (h0 * z0 + h1 * z1 + h2 * z2) ^ 2 + (h0 - h1) ^ 2 * z0 * z1
        + (h0 - h2) ^ 2 * z0 * z2 + (h1 - h2) ^ 2 * z1 * z2 := by
  ring

/-- Reindexing a shifted sum over `range N`. -/
lemma shift_A (N s : ℕ) (B v : ℕ → ℝ) :
    ∑ n ∈ range N, (if s ≤ n then B (n - s) * v n else 0)
      = ∑ m ∈ range (N - s), B m * v (m + s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    by_cases hs : s ≤ N
    · have e1 : N + 1 - s = (N - s) + 1 := by omega
      rw [e1, sum_range_succ, if_pos hs, show N - s + s = N by omega]
    · have e1 : N + 1 - s = N - s := by omega
      rw [e1, if_neg hs, add_zero]

/-- Full reindexing when `v` vanishes beyond `N`. -/
lemma shift_full (N s : ℕ) (B v : ℕ → ℝ) (hv : ∀ n, N ≤ n → v n = 0) :
    ∑ n ∈ range N, (if s ≤ n then B (n - s) * v n else 0)
      = ∑ m ∈ range N, B m * v (m + s) := by
  rw [shift_A]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le N s)) ?_
  intro m _ hm'
  have h1 : N ≤ m + s := by
    simp only [Finset.mem_range, not_lt] at hm'
    omega
  rw [hv (m + s) h1, mul_zero]

/-- Bernoulli-type lower bound `q^(-p) ≥ 1 - p(q-1)` for `q ≥ 1`, `0 ≤ p ≤ 1`. -/
lemma bern_lower (q p : ℝ) (hq : 1 ≤ q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - p * (q - 1) ≤ q ^ (-p) := by
  have hq0 : 0 < q := by linarith
  have hup : q ^ p ≤ 1 + p * (q - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := q - 1) (by linarith) hp0 hp1
    simpa using h
  have hz : 0 < q ^ p := Real.rpow_pos_of_pos hq0 p
  have ht : 0 ≤ p * (q - 1) := mul_nonneg hp0 (by linarith)
  rw [Real.rpow_neg hq0.le, ← one_div, le_div_iff₀ hz]
  rcases le_total (1 - p * (q - 1)) 0 with h | h
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hup h, sq_nonneg (p * (q - 1))]

lemma rpow_neg_succ (x : ℝ) (hx : 0 < x) (p : ℝ) :
    x ^ (-(p + 1)) = x ^ (-p) * x⁻¹ := by
  rw [show -(p + 1) = -p + -1 by ring, Real.rpow_add hx, Real.rpow_neg_one]

/-- Weight difference bound for `w_n = (n+1)^(-p)`. -/
lemma w_diff (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i j : ℕ) (hij : i ≤ j) :
    0 ≤ ((i : ℝ) + 1) ^ (-p) - ((j : ℝ) + 1) ^ (-p) ∧
      ((i : ℝ) + 1) ^ (-p) - ((j : ℝ) + 1) ^ (-p)
        ≤ p * ((j : ℝ) - (i : ℝ)) * ((i : ℝ) + 1) ^ (-(p + 1)) := by
  set x : ℝ := (i : ℝ) + 1 with hxdef
  have hx : 0 < x := by positivity
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  set q : ℝ := ((j : ℝ) + 1) / x with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef, le_div_iff₀ hx]
    linarith
  have hq0 : 0 < q := by linarith
  have hyq : ((j : ℝ) + 1) = x * q := by
    rw [hqdef]
    field_simp
  have hyp : ((j : ℝ) + 1) ^ (-p) = x ^ (-p) * q ^ (-p) := by
    rw [hyq, Real.mul_rpow hx.le hq0.le]
  have hbern := bern_lower q p hq1 hp0 hp1
  have hqle : q ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  have hxp : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx.le _
  have hdiff : x ^ (-p) - ((j : ℝ) + 1) ^ (-p) = x ^ (-p) * (1 - q ^ (-p)) := by
    rw [hyp]; ring
  have hqm : q - 1 = ((j : ℝ) - (i : ℝ)) / x := by
    rw [hqdef, hxdef]
    field_simp
    ring
  have hrhs : p * ((j : ℝ) - (i : ℝ)) * x ^ (-(p + 1)) = x ^ (-p) * (p * (q - 1)) := by
    rw [rpow_neg_succ x hx p, hqm]
    field_simp
  constructor
  · rw [hdiff]
    apply mul_nonneg hxp
    linarith
  · rw [hdiff, hrhs]
    apply mul_le_mul_of_nonneg_left _ hxp
    linarith


/-- Squared Lipschitz bound for the truncated weights `h_n = max(w_n - t, 0)`. -/
lemma lip_pair (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i j m : ℕ) (hmi : m ≤ i) (hij : i ≤ j) :
    (max (((i : ℝ) + 1) ^ (-p) - t) 0 - max (((j : ℝ) + 1) ^ (-p) - t) 0) ^ 2 * ((m : ℝ) + 1)
      ≤ p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := by
  obtain ⟨hD0, hD1⟩ := w_diff p hp0 hp1 i j hij
  have hL : |max (((i : ℝ) + 1) ^ (-p) - t) 0 - max (((j : ℝ) + 1) ^ (-p) - t) 0|
      ≤ ((i : ℝ) + 1) ^ (-p) - ((j : ℝ) + 1) ^ (-p) := by
    have h := abs_max_sub_max_le_abs (((i : ℝ) + 1) ^ (-p) - t) (((j : ℝ) + 1) ^ (-p) - t) 0
    rw [show ((i : ℝ) + 1) ^ (-p) - t - (((j : ℝ) + 1) ^ (-p) - t)
        = ((i : ℝ) + 1) ^ (-p) - ((j : ℝ) + 1) ^ (-p) by ring, abs_of_nonneg hD0] at h
    exact h
  have hXi0 : 0 ≤ ((i : ℝ) + 1) ^ (-(p + 1)) := Real.rpow_nonneg (by positivity) _
  have hXle : ((i : ℝ) + 1) ^ (-(p + 1)) ≤ ((m : ℝ) + 1) ^ (-(p + 1)) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    have : (m : ℝ) ≤ i := by exact_mod_cast hmi
    linarith
  have hid : ((m : ℝ) + 1) ^ (-(1 + 2 * p))
      = ((m : ℝ) + 1) ^ (-(p + 1)) * ((m : ℝ) + 1) ^ (-(p + 1)) * ((m : ℝ) + 1) := by
    rw [show -(1 + 2 * p) = -(p + 1) + -(p + 1) + 1 by ring,
      Real.rpow_add (by positivity), Real.rpow_add (by positivity), Real.rpow_one]
  have hsq1 : (max (((i : ℝ) + 1) ^ (-p) - t) 0 - max (((j : ℝ) + 1) ^ (-p) - t) 0) ^ 2
      ≤ (((i : ℝ) + 1) ^ (-p) - ((j : ℝ) + 1) ^ (-p)) ^ 2 := by
    nlinarith [abs_nonneg (max (((i : ℝ) + 1) ^ (-p) - t) 0 - max (((j : ℝ) + 1) ^ (-p) - t) 0),
      sq_abs (max (((i : ℝ) + 1) ^ (-p) - t) 0 - max (((j : ℝ) + 1) ^ (-p) - t) 0)]
  have hsq2 : (((i : ℝ) + 1) ^ (-p) - ((j : ℝ) + 1) ^ (-p)) ^ 2
      ≤ (p * ((j : ℝ) - (i : ℝ)) * ((i : ℝ) + 1) ^ (-(p + 1))) ^ 2 := by
    nlinarith
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hpos : 0 ≤ p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 := by positivity
  have hmain : ((i : ℝ) + 1) ^ (-(p + 1)) * ((i : ℝ) + 1) ^ (-(p + 1))
      ≤ ((m : ℝ) + 1) ^ (-(p + 1)) * ((m : ℝ) + 1) ^ (-(p + 1)) :=
    mul_self_le_mul_self hXi0 hXle
  calc (max (((i : ℝ) + 1) ^ (-p) - t) 0 - max (((j : ℝ) + 1) ^ (-p) - t) 0) ^ 2 * ((m : ℝ) + 1)
      ≤ (p * ((j : ℝ) - (i : ℝ)) * ((i : ℝ) + 1) ^ (-(p + 1))) ^ 2 * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_trans hsq1 hsq2) hm1
    _ = p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 * (((i : ℝ) + 1) ^ (-(p + 1)) * ((i : ℝ) + 1) ^ (-(p + 1)))
          * ((m : ℝ) + 1) := by ring
    _ ≤ p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 * (((m : ℝ) + 1) ^ (-(p + 1)) * ((m : ℝ) + 1) ^ (-(p + 1)))
          * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hpos) hm1
    _ = p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := by
        rw [hid]; ring


set_option maxHeartbeats 1000000 in
/-- The finite energy inequality (paper Step 3 with the weighted Lipschitz bound). -/
lemma energy_ineq_loc (R : ℕ) (a b δ h : ℕ → ℝ) (c ε p : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ a n) (hb0 : ∀ n : ℕ, 0 < b n)
    (hb : ∀ n : ℕ, b n ≤ ε * ((n : ℝ) + 1))
    (hlin : ∀ n : ℕ, a n * δ n + b n * (δ n + δ (n + 1) + δ (n + 2))
      + (if 1 ≤ n then b (n - 1) * (δ (n - 1) + δ n + δ (n + 1)) else 0)
      + (if 2 ≤ n then b (n - 2) * (δ (n - 2) + δ (n - 1) + δ n) else 0) = 0)
    (hz : ∀ n, R ≤ n → h n = 0)
    (hLip : ∀ m i j : ℕ, m ≤ i → i ≤ j →
      (h i - h j) ^ 2 * ((m : ℝ) + 1) ≤ p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p))) :
    c * ∑ n ∈ range R, h n ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
      ≤ ε / 2 * p ^ 2 * ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-(1 + 2 * p))
          * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) := by
  set B : ℕ → ℝ := fun m => b m * (δ m + δ (m + 1) + δ (m + 2)) with hB
  set v : ℕ → ℝ := fun n => h n ^ 2 * δ n with hv
  have hvz : ∀ n, R ≤ n → v n = 0 := fun n hn => by simp only [hv, hz n hn]; ring
  have hlin' : ∀ n, a n * δ n + B n + (if 1 ≤ n then B (n - 1) else 0)
      + (if 2 ≤ n then B (n - 2) else 0) = 0 := by
    intro n
    have e1 : (if 1 ≤ n then b (n - 1) * (δ (n - 1) + δ n + δ (n + 1)) else 0)
        = (if 1 ≤ n then B (n - 1) else 0) := by
      split_ifs with h1
      · simp only [hB]
        rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega]
      · rfl
    have e2 : (if 2 ≤ n then b (n - 2) * (δ (n - 2) + δ (n - 1) + δ n) else 0)
        = (if 2 ≤ n then B (n - 2) else 0) := by
      split_ifs with h2
      · simp only [hB]
        rw [show n - 2 + 1 = n - 1 by omega, show n - 2 + 2 = n by omega]
      · rfl
    have := hlin n
    rw [e1, e2] at this
    simp only [hB]
    linarith
  -- Step 3a: the regrouped identity
  have hsum0 : ∑ n ∈ range R, v n * (a n * δ n + B n + (if 1 ≤ n then B (n - 1) else 0)
      + (if 2 ≤ n then B (n - 2) else 0)) = 0 :=
    Finset.sum_eq_zero fun n _ => by rw [hlin' n, mul_zero]
  have hexp : ∑ n ∈ range R, v n * (a n * δ n + B n + (if 1 ≤ n then B (n - 1) else 0)
      + (if 2 ≤ n then B (n - 2) else 0))
      = ∑ n ∈ range R, a n * δ n * v n + ∑ n ∈ range R, B n * v n
        + ∑ n ∈ range R, (if 1 ≤ n then B (n - 1) * v n else 0)
        + ∑ n ∈ range R, (if 2 ≤ n then B (n - 2) * v n else 0) := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [hexp, shift_full R 1 B v hvz, shift_full R 2 B v hvz] at hsum0
  have hEq1 : ∑ n ∈ range R, a n * δ n * v n
      + ∑ m ∈ range R, B m * (v m + v (m + 1) + v (m + 2)) = 0 := by
    simp only [mul_add, sum_add_distrib]
    simp only [mul_comm (B _) (v _)] at hsum0 ⊢
    linarith
  -- Step 3b: the quadratic identity per index
  set P : ℕ → ℝ := fun m => h m * δ m + h (m + 1) * δ (m + 1) + h (m + 2) * δ (m + 2) with hP
  set D : ℕ → ℝ := fun m => (h m - h (m + 1)) ^ 2 * δ m * δ (m + 1)
      + (h m - h (m + 2)) ^ 2 * δ m * δ (m + 2) + (h (m + 1) - h (m + 2)) ^ 2 * δ (m + 1) * δ (m + 2)
    with hD
  have hQ : ∀ m, B m * (v m + v (m + 1) + v (m + 2)) = b m * (P m ^ 2 + D m) := by
    intro m
    simp only [hB, hv, hP, hD]
    have := quad_identity (h m) (h (m + 1)) (h (m + 2)) (δ m) (δ (m + 1)) (δ (m + 2))
    linear_combination b m * this
  have hEq2 : ∑ n ∈ range R, a n * δ n * v n + ∑ m ∈ range R, b m * (P m ^ 2 + D m) = 0 := by
    rw [← hEq1]
    congr 1
    exact sum_congr rfl fun m _ => (hQ m).symm
  -- Step 3c: `-D ≤ E`
  set E : ℕ → ℝ := fun m => 1 / 2 * ((h m - h (m + 1)) ^ 2 * (δ m ^ 2 + δ (m + 1) ^ 2)
      + (h m - h (m + 2)) ^ 2 * (δ m ^ 2 + δ (m + 2) ^ 2)
      + (h (m + 1) - h (m + 2)) ^ 2 * (δ (m + 1) ^ 2 + δ (m + 2) ^ 2)) with hE
  have hE0 : ∀ m, 0 ≤ E m := fun m => by
    simp only [hE]
    positivity
  have hDE : ∀ m, b m * (-D m) ≤ b m * E m := fun m => by
    apply mul_le_mul_of_nonneg_left _ (hb0 m).le
    have k1 : 0 ≤ (h m - h (m + 1)) ^ 2 * (δ m + δ (m + 1)) ^ 2 := by positivity
    have k2 : 0 ≤ (h m - h (m + 2)) ^ 2 * (δ m + δ (m + 2)) ^ 2 := by positivity
    have k3 : 0 ≤ (h (m + 1) - h (m + 2)) ^ 2 * (δ (m + 1) + δ (m + 2)) ^ 2 := by positivity
    have hid : E m + D m = 1 / 2 * ((h m - h (m + 1)) ^ 2 * (δ m + δ (m + 1)) ^ 2
        + (h m - h (m + 2)) ^ 2 * (δ m + δ (m + 2)) ^ 2
        + (h (m + 1) - h (m + 2)) ^ 2 * (δ (m + 1) + δ (m + 2)) ^ 2) := by
      simp only [hE, hD]
      ring
    have hsum : 0 ≤ 1 / 2 * ((h m - h (m + 1)) ^ 2 * (δ m + δ (m + 1)) ^ 2
        + (h m - h (m + 2)) ^ 2 * (δ m + δ (m + 2)) ^ 2
        + (h (m + 1) - h (m + 2)) ^ 2 * (δ (m + 1) + δ (m + 2)) ^ 2) := by positivity
    linarith
  have hDb : ∀ m, b m * D m ≤ b m * (P m ^ 2 + D m) := fun m => by
    have := mul_nonneg (hb0 m).le (sq_nonneg (P m))
    linarith
  have hT1 : ∑ m ∈ range R, b m * D m ≤ ∑ m ∈ range R, b m * (P m ^ 2 + D m) :=
    sum_le_sum fun m _ => hDb m
  have hT2 : ∑ m ∈ range R, b m * (-D m) ≤ ∑ m ∈ range R, b m * E m :=
    sum_le_sum fun m _ => hDE m
  have hneg : ∑ m ∈ range R, b m * (-D m) = -∑ m ∈ range R, b m * D m := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun m _ => by ring
  -- Step 3d: `Σ a h² δ² ≤ Σ b E`
  have hEq3 : ∑ n ∈ range R, a n * δ n * v n ≤ ∑ m ∈ range R, b m * E m := by
    linarith
  -- Step 4a: the termwise Lipschitz bound
  set X : ℕ → ℝ := fun m => ((m : ℝ) + 1) ^ (-(1 + 2 * p)) with hX
  have hterm : ∀ m, b m * E m ≤ ε / 2 * p ^ 2 * X m
      * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) := by
    intro m
    have l01 := hLip m m (m + 1) le_rfl (by omega)
    have l02 := hLip m m (m + 2) le_rfl (by omega)
    have l12 := hLip m (m + 1) (m + 2) (by omega) (by omega)
    have c01 : (((m + 1 : ℕ) : ℝ) - (m : ℝ)) ^ 2 = 1 := by push_cast; ring
    have c02 : (((m + 2 : ℕ) : ℝ) - (m : ℝ)) ^ 2 = 4 := by push_cast; ring
    have c12 : (((m + 2 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) ^ 2 = 1 := by push_cast; ring
    rw [c01] at l01
    rw [c02] at l02
    rw [c12] at l12
    have hX' : (((m : ℝ) + 1) ^ (-(1 + 2 * p))) = X m := rfl
    rw [hX'] at l01 l02 l12
    have s01 : 0 ≤ δ m ^ 2 + δ (m + 1) ^ 2 := by positivity
    have s02 : 0 ≤ δ m ^ 2 + δ (m + 2) ^ 2 := by positivity
    have s12 : 0 ≤ δ (m + 1) ^ 2 + δ (m + 2) ^ 2 := by positivity
    have q01 : (h m - h (m + 1)) ^ 2 * ((m : ℝ) + 1) * (δ m ^ 2 + δ (m + 1) ^ 2)
        ≤ p ^ 2 * X m * (δ m ^ 2 + δ (m + 1) ^ 2) :=
      (mul_le_mul_of_nonneg_right l01 s01).trans_eq (by ring)
    have q02 : (h m - h (m + 2)) ^ 2 * ((m : ℝ) + 1) * (δ m ^ 2 + δ (m + 2) ^ 2)
        ≤ 4 * (p ^ 2 * X m) * (δ m ^ 2 + δ (m + 2) ^ 2) :=
      (mul_le_mul_of_nonneg_right l02 s02).trans_eq (by ring)
    have q12 : (h (m + 1) - h (m + 2)) ^ 2 * ((m : ℝ) + 1) * (δ (m + 1) ^ 2 + δ (m + 2) ^ 2)
        ≤ p ^ 2 * X m * (δ (m + 1) ^ 2 + δ (m + 2) ^ 2) :=
      (mul_le_mul_of_nonneg_right l12 s12).trans_eq (by ring)
    have hEm : ((m : ℝ) + 1) * E m ≤ 1 / 2 * (p ^ 2 * X m * (δ m ^ 2 + δ (m + 1) ^ 2)
        + 4 * (p ^ 2 * X m) * (δ m ^ 2 + δ (m + 2) ^ 2)
        + p ^ 2 * X m * (δ (m + 1) ^ 2 + δ (m + 2) ^ 2)) := by
      have e : ((m : ℝ) + 1) * E m = 1 / 2 * ((h m - h (m + 1)) ^ 2 * ((m : ℝ) + 1)
          * (δ m ^ 2 + δ (m + 1) ^ 2)
          + (h m - h (m + 2)) ^ 2 * ((m : ℝ) + 1) * (δ m ^ 2 + δ (m + 2) ^ 2)
          + (h (m + 1) - h (m + 2)) ^ 2 * ((m : ℝ) + 1) * (δ (m + 1) ^ 2 + δ (m + 2) ^ 2)) := by
        simp only [hE]
        ring
      rw [e]
      linarith [q01, q02, q12]
    have hb' : b m * E m ≤ ε * ((m : ℝ) + 1) * E m :=
      mul_le_mul_of_nonneg_right (hb m) (hE0 m)
    calc b m * E m ≤ ε * ((m : ℝ) + 1) * E m := hb'
      _ = ε * (((m : ℝ) + 1) * E m) := by ring
      _ ≤ ε * (1 / 2 * (p ^ 2 * X m * (δ m ^ 2 + δ (m + 1) ^ 2)
          + 4 * (p ^ 2 * X m) * (δ m ^ 2 + δ (m + 2) ^ 2)
          + p ^ 2 * X m * (δ (m + 1) ^ 2 + δ (m + 2) ^ 2))) :=
        mul_le_mul_of_nonneg_left hEm hε.le
      _ = ε / 2 * p ^ 2 * X m
          * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) := by ring
  have hSum4 : ∑ m ∈ range R, b m * E m ≤ ∑ m ∈ range R, ε / 2 * p ^ 2 * X m
      * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) :=
    sum_le_sum fun m _ => hterm m
  -- Step 4b: the left side
  have hLHS : c * ∑ n ∈ range R, h n ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
      ≤ ∑ n ∈ range R, a n * δ n * v n := by
    rw [mul_sum]
    refine sum_le_sum fun n _ => ?_
    have hq : 0 ≤ h n ^ 2 * δ n ^ 2 := by positivity
    have e1 : c * (h n ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)) = c / ((n : ℝ) + 1) * (h n ^ 2 * δ n ^ 2) := by
      ring
    have e2 : a n * δ n * v n = a n * (h n ^ 2 * δ n ^ 2) := by
      simp only [hv]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (ha n) hq
  calc c * ∑ n ∈ range R, h n ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
      ≤ ∑ n ∈ range R, a n * δ n * v n := hLHS
    _ ≤ ∑ m ∈ range R, b m * E m := hEq3
    _ ≤ ∑ m ∈ range R, ε / 2 * p ^ 2 * X m
          * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) := hSum4
    _ = ε / 2 * p ^ 2 * ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-(1 + 2 * p))
          * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) := by
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by simp only [hX]; ring


lemma summable_shift_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-s)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-s)) 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith))
  simpa using h

/-- Summability of the weighted squared increments. -/
lemma summable_g (L p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (δ : ℕ → ℝ)
    (hδ : ∀ n : ℕ, |δ n| ≤ L + 2 * Real.log ((n : ℝ) + 1)) :
    Summable (fun n : ℕ => δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))) := by
  have hs1 := summable_shift_rpow (1 + 2 * p) (by linarith)
  have hs2 := summable_shift_rpow (1 + p) (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hs1.mul_left (2 * L ^ 2)).add (hs2.mul_left (32 / p ^ 2)))
  set x : ℝ := (n : ℝ) + 1 with hx_def
  have hx1 : 1 ≤ x := by
    rw [hx_def]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hx0 : 0 < x := by linarith
  have hlg0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlgb : Real.log x ≤ x ^ (p / 2) / (p / 2) :=
    Real.log_le_rpow_div (by linarith) (by linarith)
  have hxp : (x ^ (p / 2)) ^ 2 = x ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hsq : Real.log x ^ 2 ≤ 4 * x ^ p / p ^ 2 := by
    have h1 : Real.log x ^ 2 ≤ (x ^ (p / 2) / (p / 2)) ^ 2 :=
      pow_le_pow_left₀ hlg0 hlgb 2
    have h2 : (x ^ (p / 2) / (p / 2)) ^ 2 = 4 * x ^ p / p ^ 2 := by
      rw [div_pow, hxp]
      field_simp
      norm_num
    linarith
  have hδ2 : δ n ^ 2 ≤ 2 * L ^ 2 + 8 * Real.log x ^ 2 := by
    have hT : |δ n| ≤ L + 2 * Real.log x := hδ n
    have hT0 : 0 ≤ L + 2 * Real.log x := le_trans (abs_nonneg _) hT
    have h1 : δ n ^ 2 ≤ (L + 2 * Real.log x) ^ 2 := by
      nlinarith [abs_nonneg (δ n), sq_abs (δ n)]
    nlinarith [sq_nonneg (L - 2 * Real.log x)]
  have hXp : x ^ p * x ^ (-(1 + 2 * p)) = x ^ (-(1 + p)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hXnn : 0 ≤ x ^ (-(1 + 2 * p)) := Real.rpow_nonneg hx0.le _
  calc δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))
      = δ n ^ 2 * x ^ (-(1 + 2 * p)) := by rw [hx_def]
    _ ≤ (2 * L ^ 2 + 8 * Real.log x ^ 2) * x ^ (-(1 + 2 * p)) :=
        mul_le_mul_of_nonneg_right hδ2 hXnn
    _ ≤ (2 * L ^ 2 + 32 * x ^ p / p ^ 2) * x ^ (-(1 + 2 * p)) :=
        mul_le_mul_of_nonneg_right (by
          have : 8 * Real.log x ^ 2 ≤ 8 * (4 * x ^ p / p ^ 2) := by linarith
          have e : 8 * (4 * x ^ p / p ^ 2) = 32 * x ^ p / p ^ 2 := by ring
          linarith) hXnn
    _ = 2 * L ^ 2 * x ^ (-(1 + 2 * p)) + 32 / p ^ 2 * (x ^ p * x ^ (-(1 + 2 * p))) := by ring
    _ = 2 * L ^ 2 * x ^ (-(1 + 2 * p)) + 32 / p ^ 2 * x ^ (-(1 + p)) := by rw [hXp]

/-- Comparison of the weights at scale `m+1` and at a shift `m+j`, `j ≤ 2`. -/
lemma wt_bound (E : ℝ) (hE : E ≤ 3) (hE0 : 0 ≤ E) (m j : ℕ) (hj : j ≤ 2) :
    ((m : ℝ) + 1) ^ (-E) ≤ 27 * (((m + j : ℕ) : ℝ) + 1) ^ (-E) := by
  have hx : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hyle : (((m + j : ℕ) : ℝ) + 1) ≤ 3 * ((m : ℝ) + 1) := by
    have : ((m + j : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
      have : m + j ≤ m + 2 := by omega
      exact_mod_cast this
    linarith
  have hy0 : 0 < (((m + j : ℕ) : ℝ) + 1) := by positivity
  have hcmp : (3 * ((m : ℝ) + 1)) ^ (-E) ≤ (((m + j : ℕ) : ℝ) + 1) ^ (-E) :=
    Real.rpow_le_rpow_of_nonpos hy0 hyle (by linarith)
  have hmul : (3 * ((m : ℝ) + 1)) ^ (-E) = (3 : ℝ) ^ (-E) * ((m : ℝ) + 1) ^ (-E) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h3 : (3 : ℝ) ^ E ≤ 27 := by
    calc (3 : ℝ) ^ E ≤ (3 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
      _ = 27 := by norm_num
  have h3p : 0 < (3 : ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) E
  have hneg : (3 : ℝ) ^ (-E) = ((3 : ℝ) ^ E)⁻¹ := Real.rpow_neg (by norm_num) E
  have hA0 : 0 ≤ ((m : ℝ) + 1) ^ (-E) := Real.rpow_nonneg (by linarith) _
  have hB0 : 0 ≤ (((m + j : ℕ) : ℝ) + 1) ^ (-E) := Real.rpow_nonneg hy0.le _
  rw [hmul, hneg] at hcmp
  -- hcmp : (3^E)⁻¹ * A ≤ B
  have h4 : ((m : ℝ) + 1) ^ (-E) ≤ (3 : ℝ) ^ E * (((m + j : ℕ) : ℝ) + 1) ^ (-E) := by
    have := mul_le_mul_of_nonneg_left hcmp h3p.le
    rw [← mul_assoc, mul_inv_cancel₀ h3p.ne', one_mul] at this
    exact this
  nlinarith [mul_le_mul_of_nonneg_right h3 hB0]

/-- Partial sums of a shifted nonnegative summable sequence are bounded by the full sum. -/
lemma shift_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hgs : Summable g) (N j : ℕ) :
    ∑ m ∈ range N, g (m + j) ≤ ∑' n, g n := by
  have hinj : Set.InjOn (fun m : ℕ => m + j) (range N : Set ℕ) := fun a _ b _ h => by
    simpa using h
  rw [← sum_image (f := g) (s := range N) (g := fun m : ℕ => m + j)]
  · exact Summable.sum_le_tsum _ (fun n _ => hg0 n) hgs
  · intro a ha b hb hab
    simpa using hab

/-- The tail sum with the weights `(m+1)^(-E)`, `0 ≤ E ≤ 3`. -/
lemma tail_sum (E : ℝ) (hE : E ≤ 3) (hE0 : 0 ≤ E) (δ : ℕ → ℝ) (R : ℕ)
    (hgs : Summable (fun n : ℕ => δ n ^ 2 * ((n : ℝ) + 1) ^ (-E))) :
    ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2)
      ≤ 324 * ∑' n, δ n ^ 2 * ((n : ℝ) + 1) ^ (-E) := by
  set g : ℕ → ℝ := fun n => δ n ^ 2 * ((n : ℝ) + 1) ^ (-E) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hpt : ∀ (m j : ℕ), j ≤ 2 → ((m : ℝ) + 1) ^ (-E) * δ (m + j) ^ 2 ≤ 27 * g (m + j) := by
    intro m j hj
    have hw := wt_bound E hE hE0 m j hj
    have hd : 0 ≤ δ (m + j) ^ 2 := sq_nonneg _
    have e : g (m + j) = δ (m + j) ^ 2 * ((((m + j : ℕ) : ℝ) + 1)) ^ (-E) := rfl
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hw hd]
  have hA : ∀ j, j ≤ 2 → ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + j) ^ 2
      ≤ 27 * ∑' n, g n := by
    intro j hj
    calc ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + j) ^ 2
        ≤ ∑ m ∈ range R, 27 * g (m + j) := sum_le_sum fun m _ => hpt m j hj
      _ = 27 * ∑ m ∈ range R, g (m + j) := by rw [mul_sum]
      _ ≤ 27 * ∑' n, g n := mul_le_mul_of_nonneg_left (shift_le g hg0 hgs R j) (by norm_num)
  have h0 : ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ m ^ 2 ≤ 27 * ∑' n, g n := by
    simpa using hA 0 (by norm_num)
  have h1 : ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + 1) ^ 2 ≤ 27 * ∑' n, g n := hA 1 (by norm_num)
  have h2 : ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + 2) ^ 2 ≤ 27 * ∑' n, g n := hA 2 (by norm_num)
  have key : ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2)
      = 5 * (∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ m ^ 2)
        + 2 * (∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + 1) ^ 2)
        + 5 * (∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + 2) ^ 2) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [key]
  linarith


lemma w_sq_div (x : ℕ) (p : ℝ) :
    (((x : ℝ) + 1) ^ (-p)) ^ 2 / ((x : ℝ) + 1) = ((x : ℝ) + 1) ^ (-(1 + 2 * p)) := by
  have hx : 0 < (x : ℝ) + 1 := by positivity
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_neg_one,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

/-- **Energy core** (paper Section 7, Steps 3–4): the recurrence linearisation forces `δ = 0`. -/
theorem energy_core (ε c L : ℝ) (hε : 0 < ε) (hc : 0 < c) (hcε : c ≤ ε)
    (δ a b : ℕ → ℝ)
    (ha : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ a n)
    (hb0 : ∀ n : ℕ, 0 < b n) (hb : ∀ n : ℕ, b n ≤ ε * ((n : ℝ) + 1))
    (hδ : ∀ n : ℕ, |δ n| ≤ L + 2 * Real.log ((n : ℝ) + 1))
    (hlin : ∀ n : ℕ, a n * δ n + b n * (δ n + δ (n + 1) + δ (n + 2))
      + (if 1 ≤ n then b (n - 1) * (δ (n - 1) + δ n + δ (n + 1)) else 0)
      + (if 2 ≤ n then b (n - 2) * (δ (n - 2) + δ (n - 1) + δ n) else 0) = 0) :
    ∀ n : ℕ, δ n = 0 := by
  set p : ℝ := Real.sqrt (c / (324 * ε)) with hp_def
  have hcr : c / (324 * ε) ≤ 1 / 324 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hp2 : p ^ 2 = c / (324 * ε) := Real.sq_sqrt (by positivity)
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by positivity)
  have hp1 : p ≤ 1 := by nlinarith
  have hE3 : 1 + 2 * p ≤ 3 := by linarith
  have hE0 : 0 ≤ 1 + 2 * p := by linarith
  have hgs := summable_g L p hp0 hp1 δ hδ
  set S : ℝ := ∑' n, δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)) with hS
  have hkey : ∀ R : ℕ, c * ∑ n ∈ range R,
      (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
        ≤ c / 2 * S := by
    intro R
    have hz : ∀ n, R ≤ n → max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0 = 0 := by
      intro n hn
      have hRn : (R : ℝ) ≤ n := by exact_mod_cast hn
      have hle : ((n : ℝ) + 1) ^ (-p) ≤ ((R : ℝ) + 1) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      exact max_eq_right (by linarith)
    have hLip : ∀ m i j : ℕ, m ≤ i → i ≤ j →
        (max (((i : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0
          - max (((j : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * ((m : ℝ) + 1)
          ≤ p ^ 2 * ((j : ℝ) - (i : ℝ)) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) :=
      fun m i j hmi hij => lip_pair p _ hp0.le hp1 i j m hmi hij
    have h1 := energy_ineq_loc R a b δ
      (fun n : ℕ => max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) c ε p hc hε hp0.le hp1
      ha hb0 hb hlin hz hLip
    have ht := tail_sum (1 + 2 * p) hE3 hE0 δ R hgs
    have hpc : ε / 2 * p ^ 2 * (324 * S) = c / 2 * S := by
      rw [hp2]
      field_simp
    calc c * ∑ n ∈ range R,
          (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
        ≤ ε / 2 * p ^ 2 * ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-(1 + 2 * p))
            * (5 * δ m ^ 2 + 2 * δ (m + 1) ^ 2 + 5 * δ (m + 2) ^ 2) := h1
      _ ≤ ε / 2 * p ^ 2 * (324 * S) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = c / 2 * S := hpc
  have hsumN : ∀ N : ℕ, ∑ n ∈ range N, δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)) ≤ S / 2 := by
    intro N
    have hT : Tendsto (fun R : ℕ => ∑ n ∈ range N,
        (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1))
        atTop (𝓝 (∑ n ∈ range N,
          (max (((n : ℝ) + 1) ^ (-p) - 0) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1))) := by
      apply tendsto_finsetSum
      intro n _
      have hw : Tendsto (fun R : ℕ => ((R : ℝ) + 1) ^ (-p)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hp0).comp
          (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have hcont : Continuous (fun t : ℝ =>
          (max (((n : ℝ) + 1) ^ (-p) - t) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)) := by
        fun_prop
      exact (hcont.tendsto 0).comp hw
    have hlim_eq : ∑ n ∈ range N,
        (max (((n : ℝ) + 1) ^ (-p) - 0) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
          = ∑ n ∈ range N, δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)) := by
      apply sum_congr rfl
      intro n _
      have hw0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-p) := Real.rpow_nonneg (by positivity) _
      rw [sub_zero, max_eq_left hw0, ← w_sq_div n p]
      ring
    rw [hlim_eq] at hT
    refine le_of_tendsto hT ?_
    rw [Filter.eventually_atTop]
    refine ⟨N, fun R hR => ?_⟩
    have hsub : ∑ n ∈ range N,
        (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
        ≤ ∑ n ∈ range R,
        (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1) :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hR)
        (fun n _ _ => by positivity)
    have hk := hkey R
    have h2 : c * ∑ n ∈ range N,
        (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
        ≤ c * (S / 2) := by
      have : c * ∑ n ∈ range N,
          (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1)
          ≤ c * ∑ n ∈ range R,
          (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hsub hc.le
      calc _ ≤ c * ∑ n ∈ range R,
          (max (((n : ℝ) + 1) ^ (-p) - ((R : ℝ) + 1) ^ (-p)) 0) ^ 2 * δ n ^ 2 / ((n : ℝ) + 1) := this
        _ ≤ c / 2 * S := hk
        _ = c * (S / 2) := by ring
    exact (mul_le_mul_iff_of_pos_left hc).mp h2
  have hSle : S ≤ S / 2 :=
    le_of_tendsto' hgs.hasSum.tendsto_sum_nat (fun N => hsumN N)
  have hS0 : S ≤ 0 := by linarith
  intro n
  have hnn : ∀ m, 0 ≤ δ m ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := fun m => by
    have : (0 : ℝ) < ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hgle : δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)) ≤ S / 2 := by
    have hsingle : δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))
        ≤ ∑ m ∈ range (n + 1), δ m ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) :=
      single_le_sum (fun m _ => hnn m) (mem_range.mpr (Nat.lt_succ_self n))
    linarith [hsumN (n + 1)]
  have hgn : δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)) = 0 := by
    linarith [hnn n]
  have hpos : 0 < ((n : ℝ) + 1) ^ (-(1 + 2 * p)) := Real.rpow_pos_of_pos (by positivity) _
  rcases mul_eq_zero.mp hgn with h | h
  · exact (pow_eq_zero_iff two_ne_zero).mp h
  · exact absurd h hpos.ne'

end Painleve
