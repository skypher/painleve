import Painleve.StatementD
import Painleve.UniqBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniqueness for general `d`: setup and crude bounds (Section 8 of `paper.tex`)

With `T_m = v_m v_{m+1} ⋯ v_{m+d-2}`, `eq:general-recurrence` reads
`v_n + ∑_{m=n-d+2}^{n} T_m = (n+1) ε` (`eq:integrated`), where windows with a
negative index are absent. Lemma 8.1 (`lem:crude`): every positive solution
satisfies `ε/K (n+1)^{-(d-3)} ≤ v_n ≤ (n+1)ε` and `T_n ≤ (n+1)ε`, with
`K = 1 + (d-1)^{d-1} ε^{d-2}`.
-/

open Finset

namespace Painleve

variable {d : ℕ}

/-- The window product `T_m = ∏_{i<d-1} v_{m+i}`. -/
def Tw (d : ℕ) (v : ℕ → ℝ) (m : ℕ) : ℝ := ∏ i ∈ range (d - 1), v (m + i)

/-- The sum of the windows containing `n`: `∑_{j ≤ min(n, d-2)} T_{n-j}`. -/
noncomputable def Wsum (d : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (d - 1), if j ≤ n then Tw d v (n - j) else 0

lemma window_extZ (v : ℕ → ℝ) (n j : ℕ) (hj : j < d - 1) :
    ∏ i ∈ range (d - 1), extZ v ((n : ℤ) - j + i) = if j ≤ n then Tw d v (n - j) else 0 := by
  split_ifs with h
  · unfold Tw
    refine prod_congr rfl fun i _ => ?_
    rw [show ((n : ℤ) - j + i) = ((n - j + i : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring,
      extZ_of_nat]
  · refine prod_eq_zero (i := 0) (mem_range.mpr (by omega)) ?_
    exact extZ_of_neg v (by push_cast; omega)

/-- `eq:integrated`. -/
theorem genRec_iff (ε : ℝ) (v : ℕ → ℝ) :
    GenRec d ε v ↔ ∀ n : ℕ, v n + Wsum d v n = ((n : ℝ) + 1) * ε := by
  unfold GenRec Wsum
  have : ∀ n : ℕ, ∑ j ∈ range (d - 1), ∏ i ∈ range (d - 1), extZ v ((n : ℤ) - j + i)
      = ∑ j ∈ range (d - 1), if j ≤ n then Tw d v (n - j) else 0 :=
    fun n => sum_congr rfl fun j hj => window_extZ v n j (mem_range.mp hj)
  simp_rw [this]

lemma Tw_pos {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (m : ℕ) : 0 < Tw d v m :=
  prod_pos fun i _ => hv _

lemma Wsum_nonneg {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (n : ℕ) : 0 ≤ Wsum d v n :=
  sum_nonneg fun j _ => by split_ifs; exacts [(Tw_pos hv _).le, le_rfl]

/-- The window starting at `n` is the `j = 0` term of the equation at `n`. -/
lemma Tw_le_Wsum (hd : 2 ≤ d) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (n : ℕ) : Tw d v n ≤ Wsum d v n := by
  unfold Wsum
  have h0 : (0 : ℕ) ∈ range (d - 1) := mem_range.mpr (by omega)
  rw [← add_sum_erase _ _ h0, if_pos (Nat.zero_le n), Nat.sub_zero]
  have := sum_nonneg (s := (range (d - 1)).erase 0)
    (f := fun j => if j ≤ n then Tw d v (n - j) else 0)
    fun j _ => by split_ifs; exacts [(Tw_pos hv _).le, le_rfl]
  linarith

/-- **Lemma 8.1**, upper bounds. -/
theorem crude_upper (hd : 2 ≤ d) {ε : ℝ} {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (hrec : GenRec d ε v)
    (n : ℕ) : v n ≤ ((n : ℝ) + 1) * ε ∧ Tw d v n ≤ ((n : ℝ) + 1) * ε := by
  have h := (genRec_iff ε v).mp hrec n
  have hW := Wsum_nonneg (d := d) hv n
  refine ⟨by linarith, ?_⟩
  have := Tw_le_Wsum hd hv n
  have := hv n
  linarith

/-- The constant `K = 1 + (d-1)^{d-1} ε^{d-2}`. -/
noncomputable def Kc (d : ℕ) (ε : ℝ) : ℝ := 1 + ((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2)

lemma Kc_pos (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) : 0 < Kc d ε := by
  unfold Kc
  have : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  positivity

/-- Window products containing `n` factor through `v_n`. -/
lemma Tw_factor (v : ℕ → ℝ) (n j : ℕ) (hj : j < d - 1) (hjn : j ≤ n) :
    Tw d v (n - j) = v n * ∏ i ∈ (range (d - 1)).erase j, v (n - j + i) := by
  unfold Tw
  rw [← mul_prod_erase _ _ (mem_range.mpr hj), show n - j + j = n by omega]

/-- **Lemma 8.1**, lower bound: `v_n ≥ ε/K (n+1)^{-(d-3)}`. -/
theorem crude_lower (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hrec : GenRec d ε v) (n : ℕ) :
    ε / Kc d ε * ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) ≤ v n := by
  have hd2 : 2 ≤ d := by omega
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := (genRec_iff ε v).mp hrec n
  -- each other factor is at most `(d-1)(n+1)ε`
  have hfac : ∀ j ∈ range (d - 1), j ≤ n → ∀ i ∈ (range (d - 1)).erase j,
      v (n - j + i) ≤ ((d : ℝ) - 1) * ((n : ℝ) + 1) * ε := by
    intro j hj hjn i hi
    have hi' := mem_range.mp (mem_of_mem_erase hi)
    refine (crude_upper hd2 hv hrec (n - j + i)).1.trans ?_
    have : ((n - j + i : ℕ) : ℝ) + 1 ≤ ((d : ℝ) - 1) * ((n : ℝ) + 1) := by
      have h1 : ((n - j + i : ℕ) : ℝ) ≤ (n : ℝ) + ((d : ℝ) - 2) := by
        have h0 : n - j + i ≤ n + (d - 2) := by omega
        have h2 : ((n - j + i : ℕ) : ℝ) ≤ ((n + (d - 2) : ℕ) : ℝ) := Nat.cast_le.mpr h0
        have h3 : ((n + (d - 2) : ℕ) : ℝ) = (n : ℝ) + ((d : ℝ) - 2) := by
          rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ d)]; norm_num
        linarith
      nlinarith
    exact mul_le_mul_of_nonneg_right this hε.le
  -- the bracket
  set B : ℝ := 1 + ∑ j ∈ range (d - 1), if j ≤ n then ∏ i ∈ (range (d - 1)).erase j, v (n - j + i)
    else 0 with hB
  have hvB : v n * B = ((n : ℝ) + 1) * ε := by
    rw [← h, hB, Wsum, mul_add, mul_one, mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    split_ifs with hjn
    · rw [Tw_factor v n j (mem_range.mp hj) hjn]
    · rw [mul_zero]
  have hB' : B ≤ Kc d ε * ((n : ℝ) + 1) ^ (d - 2) := by
    have hsum : ∑ j ∈ range (d - 1), (if j ≤ n then ∏ i ∈ (range (d - 1)).erase j, v (n - j + i)
        else 0) ≤ ((d : ℝ) - 1) * (((d : ℝ) - 1) * ((n : ℝ) + 1) * ε) ^ (d - 2) := by
      have hsl := sum_le_card_nsmul (range (d - 1))
        (fun j => if j ≤ n then ∏ i ∈ (range (d - 1)).erase j, v (n - j + i) else 0)
        ((((d : ℝ) - 1) * ((n : ℝ) + 1) * ε) ^ (d - 2)) (fun j hj => by
          split_ifs with hjn
          · have hc : ((range (d - 1)).erase j).card = d - 2 := by
              rw [card_erase_of_mem hj, card_range]; omega
            calc ∏ i ∈ (range (d - 1)).erase j, v (n - j + i)
                ≤ ∏ i ∈ (range (d - 1)).erase j, (((d : ℝ) - 1) * ((n : ℝ) + 1) * ε) :=
                  prod_le_prod (fun i _ => (hv _).le) (fun i hi => hfac j hj hjn i hi)
              _ = _ := by rw [prod_const, hc]
          · have : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
            positivity)
      rw [card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at hsl
      exact hsl
    have hpow : (((d : ℝ) - 1) * ((n : ℝ) + 1) * ε) ^ (d - 2)
        = ((d : ℝ) - 1) ^ (d - 2) * ε ^ (d - 2) * ((n : ℝ) + 1) ^ (d - 2) := by
      rw [mul_pow, mul_pow]; ring
    have hd1 : ((d : ℝ) - 1) * ((d : ℝ) - 1) ^ (d - 2) = ((d : ℝ) - 1) ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (d - 2) := one_le_pow₀ (by linarith)
    rw [hB, Kc]
    calc 1 + _ ≤ 1 + ((d : ℝ) - 1) * (((d : ℝ) - 1) * ((n : ℝ) + 1) * ε) ^ (d - 2) := by linarith
      _ = 1 + ((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2) * ((n : ℝ) + 1) ^ (d - 2) := by
          rw [hpow, ← hd1]; ring
      _ ≤ (1 + ((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2)) * ((n : ℝ) + 1) ^ (d - 2) := by
          nlinarith [show (0 : ℝ) ≤ ((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2) by
            have : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
            positivity]
  have hKpos := Kc_pos hd2 hε
  have hBpos : 0 < B := by
    have := hv n
    nlinarith [mul_pos hn1 hε]
  -- `v_n = (n+1)ε / B ≥ (n+1)ε / (K (n+1)^{d-2})`
  have hrp : ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) * ((n : ℝ) + 1) ^ (d - 2) = (n : ℝ) + 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn1, Nat.cast_sub (by omega)]
    norm_num
  have hvn : v n = ((n : ℝ) + 1) * ε / B := by
    rw [← hvB]; field_simp
  rw [hvn, le_div_iff₀ hBpos]
  calc ε / Kc d ε * ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) * B
      ≤ ε / Kc d ε * ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) * (Kc d ε * ((n : ℝ) + 1) ^ (d - 2)) := by
        apply mul_le_mul_of_nonneg_left hB'; positivity
    _ = ε * (((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) * ((n : ℝ) + 1) ^ (d - 2)) := by
        field_simp
    _ = ((n : ℝ) + 1) * ε := by rw [hrp]; ring

end Painleve
