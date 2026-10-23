import Painleve.UniqD5

/-!
# The weighted energy bound (proof of Proposition 8.3 of `paper.tex`)

For `a_n δ_n + ∑_{m=n-d+2}^{n} b_m D_m = -r_n` with `a ≥ 0`, `0 ≤ b_m ≤ ε(m+1)`:
apply `eq:localized` with `h_n = (w_n - w_R)_+`, `w_n = (n+1)^{-p}`, bound the
source term by `∑ |r_n| w_n² |δ_n|` and the window term with the Lipschitz bound
for `h`, and let `R → ∞` (monotone in `R`).
-/

open Finset Filter Topology

namespace Painleve

/-- **Weighted energy bound.** -/
theorem energy_weighted (L : ℕ) (hL : 1 ≤ L) (p ε : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (a b δ r : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ m, b m ≤ ε * ((m : ℝ) + 1))
    (hlin : ∀ n, a n * δ n + ∑ j ∈ range L,
      (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0) = -r n)
    (hS1 : Summable (fun n : ℕ => |r n| * (((n : ℝ) + 1) ^ (-p)) ^ 2 * |δ n|))
    (hgs : Summable (fun n : ℕ => δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)))) :
    ∀ N : ℕ, ∑ n ∈ range N, a n * (((n : ℝ) + 1) ^ (-p)) ^ 2 * δ n ^ 2 ≤
      (∑' n, |r n| * (((n : ℝ) + 1) ^ (-p)) ^ 2 * |δ n|) +
        ε * p ^ 2 * ((L : ℝ) - 1) ^ 2 * L / 2 * (L * (L : ℝ) ^ (1 + 2 * p) *
          ∑' n, δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))) := by
  set w : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-p) with hw
  set B1 := ∑' n, |r n| * (((n : ℝ) + 1) ^ (-p)) ^ 2 * |δ n| with hB1
  set S := ∑' n, δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p)) with hS
  set C2 := ε * p ^ 2 * ((L : ℝ) - 1) ^ 2 * L / 2 with hC2
  have hC20 : 0 ≤ C2 := by
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    positivity
  have hw0 : ∀ n, 0 ≤ w n := fun n => Real.rpow_nonneg (by positivity) _
  -- the bound for each truncation level `R`
  have hkey : ∀ R : ℕ, ∑ n ∈ range R, a n * (max (w n - w R) 0) ^ 2 * δ n ^ 2 ≤
      B1 + C2 * (L * (L : ℝ) ^ (1 + 2 * p) * S) := by
    intro R
    set h : ℕ → ℝ := fun n => max (w n - w R) 0 with hh
    have hz : ∀ n, R ≤ n → h n = 0 := by
      intro n hn
      have hRn : (R : ℝ) ≤ n := by exact_mod_cast hn
      have hle : w n ≤ w R := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      exact max_eq_right (by linarith)
    have hhw : ∀ n, h n ≤ w n := fun n => max_le (by linarith [hw0 R]) (hw0 n)
    have hh0 : ∀ n, 0 ≤ h n := fun n => le_max_right _ _
    have hid := energy_identity L R a b δ r h hz hlin
    -- the window squares are nonnegative
    have hsq0 : 0 ≤ ∑ m ∈ range R, b m * (∑ i ∈ range L, h (m + i) * δ (m + i)) ^ 2 :=
      sum_nonneg fun m _ => mul_nonneg (hb0 m) (sq_nonneg _)
    -- source term
    have hsrc : -∑ n ∈ range R, r n * h n ^ 2 * δ n ≤ B1 := by
      have : -∑ n ∈ range R, r n * h n ^ 2 * δ n ≤ ∑ n ∈ range R, |r n| * w n ^ 2 * |δ n| := by
        rw [← sum_neg_distrib]
        refine sum_le_sum fun n _ => ?_
        have h1 : -(r n * h n ^ 2 * δ n) ≤ |r n| * h n ^ 2 * |δ n| := by
          have := neg_abs_le (r n * h n ^ 2 * δ n)
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (h n))] at this
          linarith
        have h2 : h n ^ 2 ≤ w n ^ 2 := pow_le_pow_left₀ (hh0 n) (hhw n) 2
        nlinarith [abs_nonneg (r n), abs_nonneg (δ n), mul_nonneg (abs_nonneg (r n)) (abs_nonneg (δ n))]
      refine this.trans ?_
      exact hS1.sum_le_tsum _ (fun n _ => by positivity)
    -- window term
    have hwin : -∑ m ∈ range R, b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
        (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j))) ≤
        C2 * (L * (L : ℝ) ^ (1 + 2 * p) * S) := by
      have hterm : ∀ m, -(b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
          (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j)))) ≤
          C2 * (((m : ℝ) + 1) ^ (-(1 + 2 * p)) * ∑ i ∈ range L, δ (m + i) ^ 2) := by
        intro m
        have hbm := hb m
        have hlip : ∀ i ∈ range L, ∀ j ∈ range L,
            b m * (h (m + i) - h (m + j)) ^ 2 ≤
              ε * (p ^ 2 * ((L : ℝ) - 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p))) := by
          intro i hi j hj
          have hl := lip_window p (w R) hp0.le hp1 L m i j (mem_range.mp hi) (mem_range.mp hj)
          have e : (h (m + i) - h (m + j)) =
              (max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - w R) 0 -
                max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - w R) 0) := by
            simp only [hh, hw]
          rw [e]
          calc b m * (max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - w R) 0 -
                max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - w R) 0) ^ 2
              ≤ ε * ((m : ℝ) + 1) * (max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - w R) 0 -
                max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - w R) 0) ^ 2 :=
                mul_le_mul_of_nonneg_right hbm (sq_nonneg _)
            _ = ε * ((max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - w R) 0 -
                max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - w R) 0) ^ 2 * ((m : ℝ) + 1)) := by ring
            _ ≤ ε * (p ^ 2 * ((L : ℝ) - 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p))) :=
                mul_le_mul_of_nonneg_left hl hε.le
        -- `|δδ'| ≤ (δ² + δ'²)/2`, then symmetrize
        set K : ℝ := ε * (p ^ 2 * ((L : ℝ) - 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p))) with hK
        have hK0 : 0 ≤ K := by
          have : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := Real.rpow_nonneg (by positivity) _
          positivity
        have hbound : -(b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j)))) ≤
            (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, K * ((δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2) := by
          rw [mul_sum, mul_sum, ← sum_neg_distrib, mul_sum]
          refine sum_le_sum fun i hi => ?_
          rw [mul_sum, mul_sum, ← sum_neg_distrib, mul_sum]
          refine sum_le_sum fun j hj => ?_
          have hl := hlip i hi j hj
          have hab : -(δ (m + i) * δ (m + j)) ≤ (δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2 := by
            nlinarith [sq_nonneg (δ (m + i) + δ (m + j))]
          have hab' : δ (m + i) * δ (m + j) ≤ (δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2 := by
            nlinarith [sq_nonneg (δ (m + i) - δ (m + j))]
          have hX : 0 ≤ b m * (h (m + i) - h (m + j)) ^ 2 := mul_nonneg (hb0 m) (sq_nonneg _)
          have hY : 0 ≤ (δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2 := by positivity
          nlinarith [mul_le_mul hl hY (by nlinarith [sq_nonneg (δ (m + i)), sq_nonneg (δ (m + j))]) hK0]
        refine hbound.trans (le_of_eq ?_)
        have hsym : ∑ i ∈ range L, ∑ j ∈ range L, ((δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2)
            = (L : ℝ) * ∑ i ∈ range L, δ (m + i) ^ 2 := by
          simp only [add_div, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div]
          rw [← mul_sum, ← sum_div]
          ring
        rw [show ∑ i ∈ range L, ∑ j ∈ range L, K * ((δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2)
            = K * ∑ i ∈ range L, ∑ j ∈ range L, ((δ (m + i) ^ 2 + δ (m + j) ^ 2) / 2) by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [mul_sum], hsym, hK, hC2]
        ring
      calc -∑ m ∈ range R, b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j)))
          = ∑ m ∈ range R, -(b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j)))) := by rw [sum_neg_distrib]
        _ ≤ ∑ m ∈ range R, C2 * (((m : ℝ) + 1) ^ (-(1 + 2 * p)) * ∑ i ∈ range L, δ (m + i) ^ 2) :=
            sum_le_sum fun m _ => hterm m
        _ = C2 * ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-(1 + 2 * p)) * ∑ i ∈ range L, δ (m + i) ^ 2 := by
            rw [mul_sum]
        _ ≤ C2 * (L * (L : ℝ) ^ (1 + 2 * p) * S) :=
            mul_le_mul_of_nonneg_left (tail_sumL (1 + 2 * p) (by linarith) L δ R hgs) hC20
    have hlhs : ∑ n ∈ range R, a n * (max (w n - w R) 0) ^ 2 * δ n ^ 2
        = ∑ n ∈ range R, a n * h n ^ 2 * δ n ^ 2 := rfl
    rw [hlhs]
    linarith
  -- let `R → ∞` for fixed `N`
  intro N
  have hT : Tendsto (fun R : ℕ => ∑ n ∈ range N, a n * (max (w n - w R) 0) ^ 2 * δ n ^ 2)
      atTop (𝓝 (∑ n ∈ range N, a n * (max (w n - 0) 0) ^ 2 * δ n ^ 2)) := by
    apply tendsto_finsetSum
    intro n _
    have hwR : Tendsto (fun R : ℕ => w R) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hp0).comp
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hcont : Continuous (fun s : ℝ => a n * (max (w n - s) 0) ^ 2 * δ n ^ 2) := by fun_prop
    exact (hcont.tendsto 0).comp hwR
  have hlim : ∑ n ∈ range N, a n * (max (w n - 0) 0) ^ 2 * δ n ^ 2
      = ∑ n ∈ range N, a n * (((n : ℝ) + 1) ^ (-p)) ^ 2 * δ n ^ 2 := by
    refine sum_congr rfl fun n _ => ?_
    rw [sub_zero, max_eq_left (hw0 n)]
  rw [hlim] at hT
  refine le_of_tendsto hT ?_
  rw [Filter.eventually_atTop]
  refine ⟨N, fun R hR => ?_⟩
  refine le_trans ?_ (hkey R)
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hR)
    (fun n _ _ => mul_nonneg (mul_nonneg (ha n) (sq_nonneg _)) (sq_nonneg _))

end Painleve
