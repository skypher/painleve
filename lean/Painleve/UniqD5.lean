import Painleve.UniqD4
import Painleve.Energy

/-!
# Tools for the a priori bound (Proposition 8.3 of `paper.tex`)

`LM(x,y) ≥ x/(1 + |log(y/x)|)` (`eq:lm-lower`); Lipschitz bounds for the
truncated weights `h_n = (w_n - w_R)_+`, `w_n = (n+1)^{-p}`; tail sums over
windows of length `L = d - 1`; summability of `δ_n² (n+1)^{-(1+2p)}` when
`|δ_n|` grows logarithmically.
-/

open Finset Filter Topology

namespace Painleve

/-- `eq:lm-lower`: `LM(x, y) ≥ x/(1 + |log y - log x|)`. -/
theorem logMean_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x / (1 + |Real.log y - Real.log x|) ≤ logMean x y := by
  have hden : 0 < 1 + |Real.log y - Real.log x| := by positivity
  rcases le_or_gt x y with hxy | hxy
  · refine le_trans ?_ (min_le_logMean x y hx hy)
    rw [min_eq_left hxy, div_le_iff₀ hden]
    nlinarith [abs_nonneg (Real.log y - Real.log x)]
  · -- `y < x`: `LM = (x - y)/s`, `s = log x - log y > 0`, and `x - y ≥ y s`
    set s := Real.log x - Real.log y with hs
    have hs0 : 0 < s := by rw [hs]; linarith [Real.log_lt_log hy hxy]
    have hLM : logMean x y = (x - y) / s := by
      unfold logMean
      rw [if_neg (ne_of_gt hxy)]
      rw [hs, show y - x = -(x - y) by ring, show Real.log y - Real.log x = -(Real.log x - Real.log y)
        by ring, neg_div_neg_eq]
    have habs : |Real.log y - Real.log x| = s := by
      rw [hs, abs_sub_comm, abs_of_pos hs0]
    rw [hLM, habs, div_le_div_iff₀ (by linarith) hs0]
    -- `x s ≤ (x - y)(1 + s)` ⟺ `y s ≤ x - y` ⟺ `log(x/y) ≤ x/y - 1`
    have hlog : s ≤ x / y - 1 := by
      have := Real.log_le_sub_one_of_pos (div_pos hx hy)
      rwa [Real.log_div hx.ne' hy.ne', ← hs] at this
    have : y * s ≤ x - y := by
      have h1 := mul_le_mul_of_nonneg_left hlog hy.le
      have h2 : y * (x / y - 1) = x - y := by field_simp
      linarith
    nlinarith

/-- Symmetric Lipschitz bound for truncated weights inside a window of length `L`. -/
lemma lip_window (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L m i j : ℕ) (hi : i < L) (hj : j < L) :
    (max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - t) 0 - max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - t) 0) ^ 2 *
        ((m : ℝ) + 1) ≤ p ^ 2 * ((L : ℝ) - 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hE : ∀ i' j' : ℕ, i' < L → j' < L → i' ≤ j' →
      (max ((((m + i' : ℕ) : ℝ) + 1) ^ (-p) - t) 0 - max ((((m + j' : ℕ) : ℝ) + 1) ^ (-p) - t) 0) ^ 2 *
        ((m : ℝ) + 1) ≤ p ^ 2 * ((L : ℝ) - 1) ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) := by
    intro i' j' hi' hj' hij
    have h := lip_pair p t hp0 hp1 (m + i') (m + j') m (by omega) (by omega)
    refine h.trans ?_
    have hdiff : (((m + j' : ℕ) : ℝ) - ((m + i' : ℕ) : ℝ)) ^ 2 ≤ ((L : ℝ) - 1) ^ 2 := by
      have h1 : (((m + j' : ℕ) : ℝ) - ((m + i' : ℕ) : ℝ)) = (j' : ℝ) - i' := by push_cast; ring
      rw [h1]
      have h2 : (j' : ℝ) - i' ≤ (L : ℝ) - 1 := by
        have : j' ≤ L - 1 := by omega
        have := (Nat.cast_le (α := ℝ)).mpr this
        rw [Nat.cast_sub (by omega)] at this; push_cast at this
        have : (0 : ℝ) ≤ i' := Nat.cast_nonneg _
        linarith
      have h3 : (0 : ℝ) ≤ (j' : ℝ) - i' := by
        have : (i' : ℝ) ≤ j' := by exact_mod_cast hij
        linarith
      nlinarith
    have hpos : 0 ≤ p ^ 2 * ((m : ℝ) + 1) ^ (-(1 + 2 * p)) :=
      mul_nonneg (sq_nonneg p) (Real.rpow_nonneg (by positivity) _)
    nlinarith
  rcases le_total i j with hij | hij
  · exact hE i j hi hj hij
  · have := hE j i hj hi hij
    rw [show (max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - t) 0 - max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - t) 0) ^ 2
        = (max ((((m + j : ℕ) : ℝ) + 1) ^ (-p) - t) 0 - max ((((m + i : ℕ) : ℝ) + 1) ^ (-p) - t) 0) ^ 2
        by ring]
    exact this

/-- `(m+1)^{-E} ≤ L^E (m+i+1)^{-E}` for `i < L`. -/
lemma wt_boundL (E : ℝ) (hE0 : 0 ≤ E) (L m i : ℕ) (hi : i < L) :
    ((m : ℝ) + 1) ^ (-E) ≤ (L : ℝ) ^ E * (((m + i : ℕ) : ℝ) + 1) ^ (-E) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hy0 : (0 : ℝ) < ((m + i : ℕ) : ℝ) + 1 := by positivity
  have hyle : ((m + i : ℕ) : ℝ) + 1 ≤ (L : ℝ) * ((m : ℝ) + 1) := by
    push_cast
    have : (i : ℝ) + 1 ≤ L := by exact_mod_cast hi
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hcmp : ((L : ℝ) * ((m : ℝ) + 1)) ^ (-E) ≤ (((m + i : ℕ) : ℝ) + 1) ^ (-E) :=
    Real.rpow_le_rpow_of_nonpos hy0 hyle (by linarith)
  rw [Real.mul_rpow (by linarith) hx.le, Real.rpow_neg (by linarith)] at hcmp
  have hLE : 0 < (L : ℝ) ^ E := Real.rpow_pos_of_pos (by linarith) E
  have := mul_le_mul_of_nonneg_left hcmp hLE.le
  rw [← mul_assoc, mul_inv_cancel₀ hLE.ne', one_mul] at this
  exact this

/-- Tail sums over windows: `∑_{m<R} (m+1)^{-E} ∑_{i<L} δ_{m+i}² ≤ L^{E+1} ∑' δ_n²(n+1)^{-E}`. -/
lemma tail_sumL (E : ℝ) (hE0 : 0 ≤ E) (L : ℕ) (δ : ℕ → ℝ) (R : ℕ)
    (hgs : Summable (fun n : ℕ => δ n ^ 2 * ((n : ℝ) + 1) ^ (-E))) :
    ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * ∑ i ∈ range L, δ (m + i) ^ 2
      ≤ L * (L : ℝ) ^ E * ∑' n, δ n ^ 2 * ((n : ℝ) + 1) ^ (-E) := by
  set g : ℕ → ℝ := fun n => δ n ^ 2 * ((n : ℝ) + 1) ^ (-E) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hLE0 : (0 : ℝ) ≤ (L : ℝ) ^ E := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpt : ∀ (m i : ℕ), i < L → ((m : ℝ) + 1) ^ (-E) * δ (m + i) ^ 2 ≤ (L : ℝ) ^ E * g (m + i) := by
    intro m i hi
    have hw := wt_boundL E hE0 L m i hi
    have e : g (m + i) = δ (m + i) ^ 2 * ((((m + i : ℕ) : ℝ) + 1)) ^ (-E) := rfl
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hw (sq_nonneg (δ (m + i)))]
  calc ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * ∑ i ∈ range L, δ (m + i) ^ 2
      = ∑ i ∈ range L, ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + i) ^ 2 := by
        simp_rw [mul_sum]; exact sum_comm
    _ ≤ ∑ i ∈ range L, ((L : ℝ) ^ E * ∑' n, g n) := by
        refine sum_le_sum fun i hi => ?_
        calc ∑ m ∈ range R, ((m : ℝ) + 1) ^ (-E) * δ (m + i) ^ 2
            ≤ ∑ m ∈ range R, (L : ℝ) ^ E * g (m + i) :=
              sum_le_sum fun m _ => hpt m i (mem_range.mp hi)
          _ = (L : ℝ) ^ E * ∑ m ∈ range R, g (m + i) := by rw [mul_sum]
          _ ≤ (L : ℝ) ^ E * ∑' n, g n :=
              mul_le_mul_of_nonneg_left (shift_le g hg0 hgs R i) hLE0
    _ = L * (L : ℝ) ^ E * ∑' n, g n := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- `log x ≤ (2/p) x^{p/2}` for `x ≥ 1`, `p > 0`. -/
lemma log_le_rpow_half {x p : ℝ} (hx : 1 ≤ x) (hp : 0 < p) :
    Real.log x ≤ 2 / p * x ^ (p / 2) := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (half_pos hp)
  calc Real.log x ≤ x ^ (p / 2) / (p / 2) := h
    _ = 2 / p * x ^ (p / 2) := by field_simp

/-- Summability of `δ_n² (n+1)^{-(1+2p)}` when `|δ_n| ≤ A + c log(n+1)`. -/
lemma summable_gD (A c p : ℝ) (hc : 0 ≤ c) (hp0 : 0 < p) (δ : ℕ → ℝ)
    (hδ : ∀ n : ℕ, |δ n| ≤ A + c * Real.log ((n : ℝ) + 1)) :
    Summable (fun n : ℕ => δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))) := by
  have hs1 := summable_shift_rpow (1 + 2 * p) (by linarith)
  have hs2 := summable_shift_rpow (1 + p) (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hs1.mul_left (2 * A ^ 2)).add (hs2.mul_left (2 * (c * (2 / p)) ^ 2)))
  set x : ℝ := (n : ℝ) + 1 with hx_def
  have hx1 : 1 ≤ x := by
    rw [hx_def]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hx0 : 0 < x := by linarith
  have hlog := log_le_rpow_half hx1 hp0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxp : x ^ p = (x ^ (p / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hXp : x ^ p * x ^ (-(1 + 2 * p)) = x ^ (-(1 + p)) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hXnn : 0 ≤ x ^ (-(1 + 2 * p)) := Real.rpow_nonneg hx0.le _
  have hδsq : δ n ^ 2 ≤ 2 * A ^ 2 + 2 * (c * (2 / p)) ^ 2 * x ^ p := by
    have h1 : |δ n| ≤ |A| + c * (2 / p * x ^ (p / 2)) := by
      refine (hδ n).trans ?_
      have := le_abs_self A
      have : c * Real.log x ≤ c * (2 / p * x ^ (p / 2)) := mul_le_mul_of_nonneg_left hlog hc
      rw [← hx_def]; linarith
    have h2 : δ n ^ 2 ≤ (|A| + c * (2 / p * x ^ (p / 2))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (|A| + c * (2 / p * x ^ (p / 2))) ^ 2 ≤ 2 * |A| ^ 2 + 2 * (c * (2 / p * x ^ (p / 2))) ^ 2 := by
      nlinarith [sq_nonneg (|A| - c * (2 / p * x ^ (p / 2)))]
    rw [sq_abs] at h3
    rw [hxp]
    nlinarith
  calc δ n ^ 2 * x ^ (-(1 + 2 * p))
      ≤ (2 * A ^ 2 + 2 * (c * (2 / p)) ^ 2 * x ^ p) * x ^ (-(1 + 2 * p)) :=
        mul_le_mul_of_nonneg_right hδsq hXnn
    _ = 2 * A ^ 2 * x ^ (-(1 + 2 * p)) + 2 * (c * (2 / p)) ^ 2 * (x ^ p * x ^ (-(1 + 2 * p))) := by
        ring
    _ = 2 * A ^ 2 * x ^ (-(1 + 2 * p)) + 2 * (c * (2 / p)) ^ 2 * x ^ (-(1 + p)) := by rw [hXp]

end Painleve
