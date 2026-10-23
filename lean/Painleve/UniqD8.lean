import Painleve.UniqD7

/-!
# Theorem 1.3: asymptotics and uniqueness of the positive solution

The asymptotics follow from `δ_n → 0` (Proposition 8.3) and
`q(t) ((d-1)/(εt))^{1/(d-1)} → 1`. For uniqueness, `η = log(v'/v)` is square
summable, and the energy identity with the cutoff `h = 1` on `[0, R]`, linear to
`0` on `[R, 2R]`, gives `A_n η_n² ≤ C/R` for `R ≥ n`.
-/

open Finset Filter Topology

namespace Painleve

variable {d : ℕ}

lemma tendsto_zero_of_summable_sq {f : ℕ → ℝ} (h : Summable fun n => f n ^ 2) :
    Tendsto f atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => f n ^ 2) atTop (𝓝 0) := h.tendsto_atTop_zero
  have h3 : Tendsto (fun n => Real.sqrt (f n ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  simp_rw [Real.sqrt_sq_eq_abs] at h3
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.mpr h3

/-- `q(t) ((d-1)/(εt))^{1/(d-1)} → 1` along `t = n + 1`. -/
theorem qapp_asymp (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => qn d ε n * (((d : ℝ) - 1) / (ε * ((n : ℝ) + 1))) ^ (1 / ((d : ℝ) - 1)))
      atTop (𝓝 1) := by
  have hd2 : 2 ≤ d := by omega
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  set e : ℝ := 1 / ((d : ℝ) - 1) with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by rw [he, div_lt_one hd1]; linarith
  -- `y_n = q^{d-1} (d-1)/(εt) = 1 - q/(εt) → 1`
  have hqt : Tendsto (fun n : ℕ => qn d ε n / (ε * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    -- `0 ≤ q/(εt) ≤ C t^{e-1}`
    set C : ℝ := (ε / ((d : ℝ) - 1)) ^ e / ε with hC
    have hlim : Tendsto (fun n : ℕ => C * ((n : ℝ) + 1) ^ (e - 1)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (e - 1)) atTop (𝓝 0) := by
        have h1 := tendsto_rpow_neg_atTop (y := 1 - e) (by linarith)
        have h2 := h1.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
        refine h2.congr fun n => ?_
        simp only [Function.comp]; congr 1; ring
      simpa using this.const_mul C
    refine squeeze_zero (fun n => by have := qn_pos (d := d) hε n; positivity) (fun n => ?_) hlim
    set t : ℝ := (n : ℝ) + 1 with ht
    have ht0 : 0 < t := by positivity
    have hu := qapp_upper hd2 hε ht0
    have hsplit : (ε * t / ((d : ℝ) - 1)) ^ e = (ε / ((d : ℝ) - 1)) ^ e * t ^ e := by
      rw [show ε * t / ((d : ℝ) - 1) = ε / ((d : ℝ) - 1) * t by ring,
        Real.mul_rpow (by positivity) ht0.le]
    have hte : t ^ e / t = t ^ (e - 1) := by
      rw [Real.rpow_sub ht0, Real.rpow_one]
    unfold qn
    rw [← ht, div_le_iff₀ (by positivity)]
    calc qapp d ε t ≤ (ε * t / ((d : ℝ) - 1)) ^ e := hu
      _ = C * t ^ (e - 1) * (ε * t) := by
          rw [hsplit, hC, ← hte]; field_simp
  have hy : Tendsto (fun n : ℕ => qn d ε n ^ (d - 1) * (((d : ℝ) - 1) / (ε * ((n : ℝ) + 1))))
      atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 - qn d ε n / (ε * ((n : ℝ) + 1))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hqt
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    have heq := qapp_eq (d := d) (by omega) hε (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
    unfold qn
    field_simp
    linarith
  have hroot := hy.rpow_const (p := e) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hroot
  refine hroot.congr fun n => ?_
  have hq := qn_pos (d := d) hε n
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hq.le, Nat.cast_sub (by omega), Nat.cast_one, he,
    mul_one_div_cancel hd1.ne', Real.rpow_one]

/-- **Theorem 1.3**, asymptotics. -/
theorem asymptoticsD (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hrec : GenRec d ε v) :
    Tendsto (fun n : ℕ => v n * (((d : ℝ) - 1) / (ε * ((n : ℝ) + 1))) ^ (1 / ((d : ℝ) - 1)))
      atTop (𝓝 1) := by
  have hδ := tendsto_zero_of_summable_sq (apriori hd hε hv hrec)
  have hratio : Tendsto (fun n => v n / qn d ε n) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hδ
    rw [Real.exp_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp, devD]
    rw [← Real.log_div (hv n).ne' (qn_pos hε n).ne', Real.exp_log (div_pos (hv n) (qn_pos hε n))]
  have := hratio.mul (qapp_asymp hd hε)
  rw [mul_one] at this
  refine this.congr fun n => ?_
  have := (qn_pos (d := d) hε n).ne'
  field_simp

/-! ### Uniqueness -/

/-- The cutoff: `1` on `[0, R]`, linear on `[R, 2R]`, `0` beyond. -/
noncomputable def hcut (R : ℕ) (n : ℕ) : ℝ := max 0 (min 1 (2 - (n : ℝ) / R))

lemma hcut_nonneg (R n : ℕ) : 0 ≤ hcut R n := le_max_left _ _

lemma hcut_le_one (R n : ℕ) : hcut R n ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma hcut_zero {R n : ℕ} (hR : 0 < R) (hn : 2 * R ≤ n) : hcut R n = 0 := by
  unfold hcut
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have : 2 - (n : ℝ) / R ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hR']; exact_mod_cast hn
  rw [max_eq_left (le_trans (min_le_right _ _) this)]

lemma hcut_one {R n : ℕ} (hR : 0 < R) (hn : n ≤ R) : hcut R n = 1 := by
  unfold hcut
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have : 1 ≤ 2 - (n : ℝ) / R := by
    have : (n : ℝ) / R ≤ 1 := by rw [div_le_one hR']; exact_mod_cast hn
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma hcut_lip {R : ℕ} (hR : 0 < R) (i j : ℕ) : |hcut R i - hcut R j| ≤ |(i : ℝ) - j| / R := by
  unfold hcut
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (2 - (i : ℝ) / R)) 0 (min 1 (2 - (j : ℝ) / R))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (2 - (i : ℝ) / R) 1 (2 - (j : ℝ) / R)
  simp only [sub_self, abs_zero] at h1 h2
  refine h1.trans ((max_le (abs_nonneg _) le_rfl).trans
    (h2.trans ((max_le (abs_nonneg _) le_rfl).trans (le_of_eq ?_))))
  rw [show (2 - (i : ℝ) / R) - (2 - (j : ℝ) / R) = -(((i : ℝ) - j) / R) by ring, abs_neg,
    abs_div, abs_of_pos hR']

/-- **Theorem 1.3**, uniqueness. -/
theorem uniquenessD (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {v w : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hw : ∀ n, 0 < w n) (hrv : GenRec d ε v) (hrw : GenRec d ε w) : v = w := by
  have hd2 : 2 ≤ d := by omega
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set L := d - 1 with hLdef
  have hLr : (L : ℝ) = (d : ℝ) - 1 := by rw [hLdef, Nat.cast_sub (by omega)]; norm_num
  set η : ℕ → ℝ := fun n => Real.log (w n) - Real.log (v n) with hηdef
  -- `η ∈ ℓ²`
  have hηS : Summable fun n => η n ^ 2 := by
    have h1 := apriori hd hε hv hrv
    have h2 := apriori hd hε hw hrw
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((h1.add h2).mul_left 2)
    have e : η n = devD d ε w n - devD d ε v n := by simp only [hηdef, devD]; ring
    rw [e]
    nlinarith [sq_nonneg (devD d ε w n + devD d ε v n)]
  set S := ∑' n, η n ^ 2 with hS
  set A : ℕ → ℝ := fun n => logMean (v n) (w n) with hAdef
  set B : ℕ → ℝ := fun m => logMean (Tw d v m) (Tw d w m) with hBdef
  have hA0 : ∀ n, 0 < A n := fun n =>
    lt_of_lt_of_le (lt_min (hv n) (hw n)) (min_le_logMean _ _ (hv n) (hw n))
  have hB0 : ∀ m, 0 ≤ B m := fun m =>
    (lt_of_lt_of_le (lt_min (Tw_pos hv m) (Tw_pos hw m))
      (min_le_logMean _ _ (Tw_pos hv m) (Tw_pos hw m))).le
  have hB : ∀ m, B m ≤ ε * ((m : ℝ) + 1) := fun m => by
    refine (logMean_le_max _ _ (Tw_pos hv m) (Tw_pos hw m)).trans (max_le ?_ ?_)
    · rw [mul_comm]; exact (crude_upper hd2 hv hrv m).2
    · rw [mul_comm]; exact (crude_upper hd2 hw hrw m).2
  -- the linearized system without source
  have hlin : ∀ n, A n * η n + ∑ j ∈ range L,
      (if j ≤ n then B (n - j) * ∑ i ∈ range L, η (n - j + i) else 0) = -(fun _ => (0 : ℝ)) n := by
    intro n
    have h1 : A n * η n = w n - v n := logMean_mul _ _ (hv n) (hw n)
    have h2 : ∀ m, B m * ∑ i ∈ range L, η (m + i) = Tw d w m - Tw d v m := by
      intro m
      have := logMean_mul _ _ (Tw_pos (d := d) hv m) (Tw_pos (d := d) hw m)
      rw [log_Tw hw, log_Tw hv, ← sum_sub_distrib] at this
      exact this
    have ev := (genRec_iff ε v).mp hrv n
    have ew := (genRec_iff ε w).mp hrw n
    rw [h1]
    have hW : ∑ j ∈ range L, (if j ≤ n then B (n - j) * ∑ i ∈ range L, η (n - j + i) else 0)
        = Wsum d w n - Wsum d v n := by
      unfold Wsum
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      split_ifs
      · exact h2 (n - j)
      · ring
    rw [hW]
    simp only [neg_zero]
    linarith
  -- the cutoff estimate
  have hest : ∀ n R : ℕ, 0 < R → n ≤ R → A n * η n ^ 2 ≤ ε * (L : ℝ) ^ 4 * S / R := by
    intro n R hR hnR
    have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    set h := hcut R with hh
    have hz : ∀ k, 2 * R ≤ k → h k = 0 := fun k hk => hcut_zero hR hk
    have hid := energy_identity L (2 * R) A B η (fun _ => 0) h hz hlin
    simp only [zero_mul, sum_const_zero, neg_zero, zero_sub] at hid
    have hsq0 : 0 ≤ ∑ m ∈ range (2 * R), B m * (∑ i ∈ range L, h (m + i) * η (m + i)) ^ 2 :=
      sum_nonneg fun m _ => mul_nonneg (hB0 m) (sq_nonneg _)
    -- the single term at `n`
    have hn : A n * η n ^ 2 ≤ ∑ k ∈ range (2 * R), A k * h k ^ 2 * η k ^ 2 := by
      have hmem : n ∈ range (2 * R) := mem_range.mpr (by omega)
      have := single_le_sum (f := fun k => A k * h k ^ 2 * η k ^ 2)
        (fun k _ => mul_nonneg (mul_nonneg (hA0 k).le (sq_nonneg _)) (sq_nonneg _)) hmem
      simp only [hh, hcut_one hR hnR, one_pow, mul_one] at this
      exact this
    -- the window term
    have hwin : -∑ m ∈ range (2 * R), B m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
        (h (m + i) - h (m + j)) ^ 2 * (η (m + i) * η (m + j))) ≤ ε * (L : ℝ) ^ 4 * S / R := by
      have hterm : ∀ m ∈ range (2 * R), -(B m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
          (h (m + i) - h (m + j)) ^ 2 * (η (m + i) * η (m + j)))) ≤
          ε * (L : ℝ) ^ 3 / R * ∑ i ∈ range L, η (m + i) ^ 2 := by
        intro m hm
        have hm' := mem_range.mp hm
        have hBm : B m ≤ 2 * R * ε := by
          refine (hB m).trans ?_
          have : (m : ℝ) + 1 ≤ 2 * R := by
            have : m + 1 ≤ 2 * R := hm'
            exact_mod_cast this
          nlinarith
        set K : ℝ := 2 * R * ε * ((L : ℝ) / R) ^ 2 with hK
        have hK0 : 0 ≤ K := by positivity
        have hlip : ∀ i ∈ range L, ∀ j ∈ range L, B m * (h (m + i) - h (m + j)) ^ 2 ≤ K := by
          intro i hi j hj
          have hl := hcut_lip hR (m + i) (m + j)
          have hij : |((m + i : ℕ) : ℝ) - ((m + j : ℕ) : ℝ)| ≤ L := by
            push_cast
            rw [show (m : ℝ) + i - (m + j) = (i : ℝ) - j by ring, abs_le]
            have hi' : (i : ℝ) < L := by exact_mod_cast mem_range.mp hi
            have hj' : (j : ℝ) < L := by exact_mod_cast mem_range.mp hj
            constructor <;> linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i),
              (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
          have hd2' : (h (m + i) - h (m + j)) ^ 2 ≤ ((L : ℝ) / R) ^ 2 := by
            have : |h (m + i) - h (m + j)| ≤ (L : ℝ) / R :=
              hl.trans (div_le_div_of_nonneg_right hij hR'.le)
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          calc B m * (h (m + i) - h (m + j)) ^ 2 ≤ (2 * R * ε) * ((L : ℝ) / R) ^ 2 :=
                mul_le_mul hBm hd2' (sq_nonneg _) (by positivity)
            _ = K := rfl
        have hbound : -(B m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (η (m + i) * η (m + j)))) ≤
            (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, K * ((η (m + i) ^ 2 + η (m + j) ^ 2) / 2) := by
          rw [mul_sum, mul_sum, ← sum_neg_distrib, mul_sum]
          refine sum_le_sum fun i hi => ?_
          rw [mul_sum, mul_sum, ← sum_neg_distrib, mul_sum]
          refine sum_le_sum fun j hj => ?_
          have hl := hlip i hi j hj
          have hab : -(η (m + i) * η (m + j)) ≤ (η (m + i) ^ 2 + η (m + j) ^ 2) / 2 := by
            nlinarith [sq_nonneg (η (m + i) + η (m + j))]
          have hab' : η (m + i) * η (m + j) ≤ (η (m + i) ^ 2 + η (m + j) ^ 2) / 2 := by
            nlinarith [sq_nonneg (η (m + i) - η (m + j))]
          have hX : 0 ≤ B m * (h (m + i) - h (m + j)) ^ 2 := mul_nonneg (hB0 m) (sq_nonneg _)
          have hY : 0 ≤ (η (m + i) ^ 2 + η (m + j) ^ 2) / 2 := by positivity
          nlinarith [mul_le_mul hl hY (by nlinarith [sq_nonneg (η (m + i)), sq_nonneg (η (m + j))]) hK0]
        refine hbound.trans (le_of_eq ?_)
        have hsym : ∑ i ∈ range L, ∑ j ∈ range L, ((η (m + i) ^ 2 + η (m + j) ^ 2) / 2)
            = (L : ℝ) * ∑ i ∈ range L, η (m + i) ^ 2 := by
          simp only [add_div, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div]
          rw [← mul_sum, ← sum_div]
          ring
        rw [show ∑ i ∈ range L, ∑ j ∈ range L, K * ((η (m + i) ^ 2 + η (m + j) ^ 2) / 2)
            = K * ∑ i ∈ range L, ∑ j ∈ range L, ((η (m + i) ^ 2 + η (m + j) ^ 2) / 2) by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [mul_sum], hsym, hK]
        field_simp
      have hshift : ∑ m ∈ range (2 * R), ∑ i ∈ range L, η (m + i) ^ 2 ≤ L * S := by
        rw [sum_comm]
        calc ∑ i ∈ range L, ∑ m ∈ range (2 * R), η (m + i) ^ 2 ≤ ∑ i ∈ range L, S :=
              sum_le_sum fun i _ => shift_le (fun n => η n ^ 2) (fun n => sq_nonneg _) hηS _ i
          _ = L * S := by rw [sum_const, card_range, nsmul_eq_mul]
      calc -∑ m ∈ range (2 * R), B m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (η (m + i) * η (m + j)))
          = ∑ m ∈ range (2 * R), -(B m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (η (m + i) * η (m + j)))) := by rw [sum_neg_distrib]
        _ ≤ ∑ m ∈ range (2 * R), ε * (L : ℝ) ^ 3 / R * ∑ i ∈ range L, η (m + i) ^ 2 :=
            sum_le_sum hterm
        _ = ε * (L : ℝ) ^ 3 / R * ∑ m ∈ range (2 * R), ∑ i ∈ range L, η (m + i) ^ 2 := by
            rw [mul_sum]
        _ ≤ ε * (L : ℝ) ^ 3 / R * (L * S) :=
            mul_le_mul_of_nonneg_left hshift (by positivity)
        _ = ε * (L : ℝ) ^ 4 * S / R := by ring
    linarith
  -- let `R → ∞`
  funext n
  have hle : A n * η n ^ 2 ≤ 0 := by
    have hT : Tendsto (fun R : ℕ => ε * (L : ℝ) ^ 4 * S / R) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (ε * (L : ℝ) ^ 4 * S)
      exact this
    refine ge_of_tendsto hT ?_
    rw [Filter.eventually_atTop]
    exact ⟨n + 1, fun R hR => hest n R (by omega) (by omega)⟩
  have h0 : η n ^ 2 = 0 := by
    have := mul_nonneg (hA0 n).le (sq_nonneg (η n))
    have h' : A n * η n ^ 2 = 0 := le_antisymm hle this
    rcases mul_eq_zero.mp h' with h | h
    · exact absurd h (hA0 n).ne'
    · exact h
  have hη0 : η n = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h0
  simp only [hηdef, sub_eq_zero] at hη0
  exact (Real.log_injOn_pos (hv n) (hw n) hη0.symm)

end Painleve
