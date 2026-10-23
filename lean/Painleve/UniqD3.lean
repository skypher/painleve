import Painleve.UniqD2

/-!
# Lemma 8.2 (`lem:reference`): the approximate solution and its residual

`q_n = q(n+1)`, `Q_m = q_m ⋯ q_{m+d-2}`, `r_n = q_n + ∑_{m=n-d+2}^{n} Q_m - (n+1)ε`.
For `t ≥ 1`: `q(1) t^{1/(d-1)} ≤ q(t) ≤ (εt/(d-1))^{1/(d-1)}`, `q(1) ≥ ε/K`;
`Q_m ≤ (m+1)ε`; and `|r_n| ≤ 6 ε (d-1)^4/(n+1)` (the first-order Taylor terms
cancel). The paper records the constant `4`; any `C/(n+1)` serves the a priori
bound.
-/

open Set Filter Topology Finset

namespace Painleve

variable {d : ℕ}

/-- `q_m = q(m+1)`. -/
noncomputable def qn (d : ℕ) (ε : ℝ) (m : ℕ) : ℝ := qapp d ε ((m : ℝ) + 1)

lemma qn_pos {ε : ℝ} (hε : 0 < ε) (m : ℕ) : 0 < qn d ε m := qapp_pos hε (by positivity)

lemma qapp_le {ε t : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (ht : 0 < t) : qapp d ε t ≤ ε * t := by
  have h := qapp_eq (d := d) hd hε ht
  have hq := qapp_pos (d := d) hε ht
  have : 0 ≤ ((d : ℝ) - 1) * qapp d ε t ^ (d - 1) := by
    have : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    positivity
  linarith

lemma qapp_pow_le {ε t : ℝ} (hd : 2 ≤ d) (hε : 0 < ε) (ht : 0 < t) :
    ((d : ℝ) - 1) * qapp d ε t ^ (d - 1) ≤ ε * t := by
  have h := qapp_eq (d := d) (by omega) hε ht
  have hq := qapp_pos (d := d) hε ht
  linarith

/-- `Q_m ≤ (m+1)ε`. -/
theorem Qm_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (m : ℕ) : Tw d (qn d ε) m ≤ ((m : ℝ) + 1) * ε := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set t : ℝ := (m : ℝ) + (d - 1 : ℕ) with ht
  have htpos : 0 < t := by
    have : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
    rw [ht]; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  -- every factor is at most `q(m + d - 1)`
  have hfac : Tw d (qn d ε) m ≤ qapp d ε t ^ (d - 1) := by
    unfold Tw
    calc ∏ i ∈ range (d - 1), qn d ε (m + i) ≤ ∏ i ∈ range (d - 1), qapp d ε t :=
          prod_le_prod (fun i _ => (qn_pos hε _).le) (fun i hi => by
            unfold qn
            apply qapp_mono hε
            have := mem_range.mp hi
            rw [ht]; push_cast
            have : (i : ℝ) + 1 ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast this
            linarith)
      _ = qapp d ε t ^ (d - 1) := by rw [prod_const, card_range]
  have hpow := qapp_pow_le hd hε htpos
  have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have : qapp d ε t ^ (d - 1) ≤ ε * t / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  refine hfac.trans (this.trans ?_)
  rw [div_le_iff₀ (by linarith), ht, hc]
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    (by linarith : (0 : ℝ) ≤ (d : ℝ) - 2)) hε.le]

/-- The residual `r_n`. -/
noncomputable def resid (d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  qn d ε n + Wsum d (qn d ε) n - ((n : ℝ) + 1) * ε

/-- The crude residual bound `|r_n| ≤ (d-1)(n+1)ε`. -/
lemma resid_crude (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    |resid d ε n| ≤ ((d : ℝ) - 1) * (((n : ℝ) + 1) * ε) := by
  have hq := qn_pos (d := d) hε n
  have hqle : qn d ε n ≤ ((n : ℝ) + 1) * ε := by
    unfold qn; rw [mul_comm]; exact qapp_le (by omega) hε (by positivity)
  have hW := Wsum_nonneg (d := d) (v := qn d ε) (qn_pos hε) n
  have hWle : Wsum d (qn d ε) n ≤ ((d : ℝ) - 1) * (((n : ℝ) + 1) * ε) := by
    unfold Wsum
    have hsl := sum_le_card_nsmul (range (d - 1))
      (fun j => if j ≤ n then Tw d (qn d ε) (n - j) else 0) (((n : ℝ) + 1) * ε) (fun j _ => by
        split_ifs with hjn
        · refine (Qm_le hd hε (n - j)).trans ?_
          have : ((n - j : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n j
          nlinarith
        · positivity)
    rw [card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at hsl
    exact hsl
  unfold resid
  rw [abs_le]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  constructor <;> nlinarith [mul_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity) hε]

/-! ### The second-order expansion of the windows -/

/-- `L_j(x) = ∑_k log q(t + x (k - j))`. -/
noncomputable def Lj (d : ℕ) (ε t : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (d - 1), Real.log (qapp d ε (t + x * ((k : ℝ) - j)))

noncomputable def Lj1 (d : ℕ) (ε t : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (d - 1), ((k : ℝ) - j) * fp d ε (t + x * ((k : ℝ) - j))

noncomputable def Lj2 (d : ℕ) (ε t : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (d - 1), ((k : ℝ) - j) ^ 2 * fpp d ε (t + x * ((k : ℝ) - j))

lemma kj_abs {j k : ℕ} (hj : j < d - 1) (hk : k < d - 1) : |(k : ℝ) - j| ≤ (d : ℝ) - 2 := by
  have h1 : (k : ℝ) ≤ (d : ℝ) - 2 := by
    have : k ≤ d - 2 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  have h2 : (j : ℝ) ≤ (d : ℝ) - 2 := by
    have : j ≤ d - 2 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

lemma arg_bounds (hd : 2 ≤ d) {t x : ℝ} (ht : 2 * ((d : ℝ) - 1) ≤ t) {j k : ℕ} (hj : j < d - 1)
    (hk : k < d - 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    t / 2 ≤ t + x * ((k : ℝ) - j) ∧ t + x * ((k : ℝ) - j) ≤ 3 * t / 2 := by
  have h := kj_abs (d := d) hj hk
  have hx1 : |x * ((k : ℝ) - j)| ≤ (d : ℝ) - 2 := by
    rw [abs_mul, abs_of_nonneg hx.1]
    calc x * |(k : ℝ) - j| ≤ 1 * ((d : ℝ) - 2) :=
          mul_le_mul hx.2 h (abs_nonneg _) zero_le_one
      _ = (d : ℝ) - 2 := one_mul _
  rw [abs_le] at hx1
  constructor <;> linarith

lemma hasDerivAt_Lj (hd : 2 ≤ d) {ε t x : ℝ} (hε : 0 < ε) (ht : 2 * ((d : ℝ) - 1) ≤ t) {j : ℕ}
    (hj : j < d - 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (Lj d ε t j) (Lj1 d ε t j x) x := by
  have ht0 : 0 < t := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold Lj Lj1
  refine HasDerivAt.fun_sum fun k hk => ?_
  have hs := (arg_bounds hd ht hj (mem_range.mp hk) hx).1
  have hpos : 0 < t + x * ((k : ℝ) - j) := by linarith
  have h1 := hasDerivAt_logq (d := d) hε hpos
  have h2 : HasDerivAt (fun y : ℝ => t + y * ((k : ℝ) - j)) ((k : ℝ) - j) x := by
    simpa using ((hasDerivAt_id x).mul_const ((k : ℝ) - j)).const_add t
  refine (h1.comp x h2).congr_deriv ?_
  ring

lemma hasDerivAt_Lj1 (hd : 2 ≤ d) {ε t x : ℝ} (hε : 0 < ε) (ht : 2 * ((d : ℝ) - 1) ≤ t) {j : ℕ}
    (hj : j < d - 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (Lj1 d ε t j) (Lj2 d ε t j x) x := by
  have ht0 : 0 < t := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold Lj1 Lj2
  refine HasDerivAt.fun_sum fun k hk => ?_
  have hs := (arg_bounds hd ht hj (mem_range.mp hk) hx).1
  have hpos : 0 < t + x * ((k : ℝ) - j) := by linarith
  have h1 := hasDerivAt_fp hd hε hpos
  have h2 : HasDerivAt (fun y : ℝ => t + y * ((k : ℝ) - j)) ((k : ℝ) - j) x := by
    simpa using ((hasDerivAt_id x).mul_const ((k : ℝ) - j)).const_add t
  refine ((h1.comp x h2).const_mul ((k : ℝ) - j)).congr_deriv ?_
  ring

/-- The pieces of the second derivative are `O(1/t)` and `O(1/t²)`. -/
lemma Lj_bounds (hd : 2 ≤ d) {ε t x : ℝ} (hε : 0 < ε) (ht : 2 * ((d : ℝ) - 1) ≤ t) {j : ℕ}
    (hj : j < d - 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |Lj1 d ε t j x| ≤ 2 * ((d : ℝ) - 1) ^ 2 / t ∧ |Lj2 d ε t j x| ≤ 4 * ((d : ℝ) - 1) ^ 4 / t ^ 2 ∧
      Real.exp (Lj d ε t j x) ≤ 3 * ε * t / (2 * ((d : ℝ) - 1)) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have hcard : ((range (d - 1)).card : ℝ) = (d : ℝ) - 1 := by
    rw [card_range, Nat.cast_sub (by omega)]; norm_num
  -- per-factor bounds
  have hfp : ∀ k ∈ range (d - 1), 0 < fp d ε (t + x * ((k : ℝ) - j)) ∧
      fp d ε (t + x * ((k : ℝ) - j)) ≤ 2 / t := by
    intro k hk
    have hs := arg_bounds hd ht hj (mem_range.mp hk) hx
    have hpos : 0 < t + x * ((k : ℝ) - j) := by linarith
    obtain ⟨h1, h2⟩ := fp_bounds hd hε hpos
    refine ⟨h1, h2.trans ?_⟩
    rw [div_le_div_iff₀ hpos ht0]; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold Lj1
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have := sum_le_card_nsmul (range (d - 1))
      (fun k => |((k : ℝ) - j) * fp d ε (t + x * ((k : ℝ) - j))|) (((d : ℝ) - 1) * (2 / t))
      (fun k hk => by
        rw [abs_mul, abs_of_pos (hfp k hk).1]
        exact mul_le_mul ((kj_abs hj (mem_range.mp hk)).trans (by linarith)) (hfp k hk).2
          (hfp k hk).1.le (by linarith))
    rw [nsmul_eq_mul, hcard] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  · unfold Lj2
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have := sum_le_card_nsmul (range (d - 1))
      (fun k => |((k : ℝ) - j) ^ 2 * fpp d ε (t + x * ((k : ℝ) - j))|)
      (((d : ℝ) - 1) ^ 2 * (((d : ℝ) - 1) * (2 / t) ^ 2)) (fun k hk => by
        have hs := arg_bounds hd ht hj (mem_range.mp hk) hx
        have hpos : 0 < t + x * ((k : ℝ) - j) := by linarith
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hkj : ((k : ℝ) - j) ^ 2 ≤ ((d : ℝ) - 1) ^ 2 := by
          have := kj_abs (d := d) hj (mem_range.mp hk)
          have h' : |(k : ℝ) - j| ≤ (d : ℝ) - 1 := by linarith
          nlinarith [abs_nonneg ((k : ℝ) - j), sq_abs ((k : ℝ) - j)]
        have hpp : |fpp d ε (t + x * ((k : ℝ) - j))| ≤ ((d : ℝ) - 1) * (2 / t) ^ 2 := by
          refine (fpp_bound hd hε hpos).trans ?_
          have h2 := (hfp k hk).2
          have h1 := (hfp k hk).1
          have : fp d ε (t + x * ((k : ℝ) - j)) ^ 2 ≤ (2 / t) ^ 2 :=
            pow_le_pow_left₀ h1.le h2 2
          nlinarith
        exact mul_le_mul hkj hpp (abs_nonneg _) (by positivity))
    rw [nsmul_eq_mul, hcard] at this
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  · -- `exp L_j = ∏ q(s_k) ≤ q(3t/2)^{d-1} ≤ (3εt/2)/(d-1)`
    have hexp : Real.exp (Lj d ε t j x) = ∏ k ∈ range (d - 1), qapp d ε (t + x * ((k : ℝ) - j)) := by
      unfold Lj
      rw [Real.exp_sum]
      refine prod_congr rfl fun k hk => ?_
      have hs := arg_bounds hd ht hj (mem_range.mp hk) hx
      exact Real.exp_log (qapp_pos hε (by linarith))
    have h32 : 0 < 3 * t / 2 := by positivity
    have hle : ∏ k ∈ range (d - 1), qapp d ε (t + x * ((k : ℝ) - j)) ≤ qapp d ε (3 * t / 2) ^ (d - 1) := by
      calc ∏ k ∈ range (d - 1), qapp d ε (t + x * ((k : ℝ) - j))
          ≤ ∏ k ∈ range (d - 1), qapp d ε (3 * t / 2) :=
            prod_le_prod (fun k hk => (qapp_pos hε (by
              have hs := arg_bounds hd ht hj (mem_range.mp hk) hx; linarith)).le)
              (fun k hk => qapp_mono hε (arg_bounds hd ht hj (mem_range.mp hk) hx).2)
        _ = qapp d ε (3 * t / 2) ^ (d - 1) := by rw [prod_const, card_range]
    have hpow := qapp_pow_le hd hε h32
    rw [hexp]
    refine hle.trans ?_
    rw [le_div_iff₀ (by linarith)]
    nlinarith

/-- `|P_j(1) - P_j(0) - P_j'(0)| ≤ 6 ε (d-1)^3 / t`. -/
theorem window_taylor (hd : 2 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ((d : ℝ) - 1) ≤ t) {j : ℕ}
    (hj : j < d - 1) :
    |Real.exp (Lj d ε t j 1) - Real.exp (Lj d ε t j 0) - Real.exp (Lj d ε t j 0) * Lj1 d ε t j 0|
      ≤ 6 * ε * ((d : ℝ) - 1) ^ 3 / t := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have h := taylor2 (g := fun x => Real.exp (Lj d ε t j x))
    (g' := fun x => Real.exp (Lj d ε t j x) * Lj1 d ε t j x)
    (g'' := fun x => Real.exp (Lj d ε t j x) * Lj1 d ε t j x * Lj1 d ε t j x +
      Real.exp (Lj d ε t j x) * Lj2 d ε t j x) (M := 12 * ε * ((d : ℝ) - 1) ^ 3 / t)
    (fun x hx => (hasDerivAt_Lj hd hε ht hj hx).exp)
    (fun x hx => ((hasDerivAt_Lj hd hε ht hj hx).exp.mul (hasDerivAt_Lj1 hd hε ht hj hx)))
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := Lj_bounds hd hε ht hj hx
      have hE := Real.exp_pos (Lj d ε t j x)
      have hsum : |Real.exp (Lj d ε t j x) * Lj1 d ε t j x * Lj1 d ε t j x +
          Real.exp (Lj d ε t j x) * Lj2 d ε t j x|
          ≤ Real.exp (Lj d ε t j x) * (|Lj1 d ε t j x| ^ 2 + |Lj2 d ε t j x|) := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hE, sq]
        ring
      refine hsum.trans ?_
      have hL1sq : |Lj1 d ε t j x| ^ 2 ≤ (2 * ((d : ℝ) - 1) ^ 2 / t) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc Real.exp (Lj d ε t j x) * (|Lj1 d ε t j x| ^ 2 + |Lj2 d ε t j x|)
          ≤ (3 * ε * t / (2 * ((d : ℝ) - 1))) *
              ((2 * ((d : ℝ) - 1) ^ 2 / t) ^ 2 + 4 * ((d : ℝ) - 1) ^ 4 / t ^ 2) :=
            mul_le_mul h3 (add_le_add hL1sq h2) (by positivity) (by positivity)
        _ = 12 * ε * ((d : ℝ) - 1) ^ 3 / t := by
            field_simp
            ring)
  refine h.trans (le_of_eq ?_)
  ring

lemma sum_kj_zero (L : ℕ) : ∑ j ∈ range L, ∑ k ∈ range L, ((k : ℝ) - j) = 0 := by
  have e : ∑ j ∈ range L, ∑ k ∈ range L, ((k : ℝ) - j)
      = ∑ j ∈ range L, ((∑ k ∈ range L, (k : ℝ)) - L * j) := by
    refine sum_congr rfl fun j _ => ?_
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [e, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
  ring

/-- **Lemma 8.2**, residual: `|r_n| ≤ 6 ε (d-1)^4 / (n+1)`. -/
theorem resid_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    |resid d ε n| ≤ 6 * ε * ((d : ℝ) - 1) ^ 4 / ((n : ℝ) + 1) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  set t : ℝ := (n : ℝ) + 1 with htdef
  have ht0 : 0 < t := by positivity
  by_cases hbig : 2 * ((d : ℝ) - 1) ≤ t
  · have hjn : ∀ j, j < d - 1 → j ≤ n := by
      intro j hj
      have h2 : ((2 * (d - 1) : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; linarith
      have : 2 * (d - 1) ≤ n + 1 := by exact_mod_cast h2
      omega
    have hq := qapp_pos (d := d) hε ht0
    have h1 : ∀ j ∈ range (d - 1), Real.exp (Lj d ε t j 1) = Tw d (qn d ε) (n - j) := by
      intro j hj
      unfold Lj Tw
      rw [Real.exp_sum]
      refine prod_congr rfl fun k hk => ?_
      have hjn' := hjn j (mem_range.mp hj)
      have hpos : 0 < qn d ε (n - j + k) := qn_pos hε _
      rw [one_mul]
      unfold qn at hpos ⊢
      rw [show t + ((k : ℝ) - j) = ((n - j + k : ℕ) : ℝ) + 1 by
        rw [htdef]; push_cast [Nat.cast_sub hjn']; ring]
      exact Real.exp_log hpos
    have h0 : ∀ j ∈ range (d - 1), Real.exp (Lj d ε t j 0) = qapp d ε t ^ (d - 1) := by
      intro j _
      unfold Lj
      rw [Real.exp_sum]
      simp_rw [zero_mul, add_zero, Real.exp_log hq]
      rw [prod_const, card_range]
    have hL1 : ∀ j ∈ range (d - 1), Lj1 d ε t j 0 = fp d ε t * ∑ k ∈ range (d - 1), ((k : ℝ) - j) := by
      intro j _
      unfold Lj1
      simp_rw [zero_mul, add_zero]
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      ring
    have hW : Wsum d (qn d ε) n = ∑ j ∈ range (d - 1), Real.exp (Lj d ε t j 1) := by
      unfold Wsum
      refine sum_congr rfl fun j hj => ?_
      rw [if_pos (hjn j (mem_range.mp hj)), h1 j hj]
    have hqe := qapp_eq (d := d) (by omega) hε ht0
    have hcard : ((range (d - 1)).card : ℝ) = (d : ℝ) - 1 := by
      rw [card_range, Nat.cast_sub (by omega)]; norm_num
    have hres : resid d ε n = ∑ j ∈ range (d - 1),
        (Real.exp (Lj d ε t j 1) - Real.exp (Lj d ε t j 0) -
          Real.exp (Lj d ε t j 0) * Lj1 d ε t j 0) := by
      have hs0 : ∑ j ∈ range (d - 1), Real.exp (Lj d ε t j 0) = ((d : ℝ) - 1) * qapp d ε t ^ (d - 1) := by
        rw [sum_congr rfl h0, sum_const, nsmul_eq_mul, hcard]
      have hs1 : ∑ j ∈ range (d - 1), Real.exp (Lj d ε t j 0) * Lj1 d ε t j 0 = 0 := by
        rw [sum_congr rfl fun j hj => by rw [h0 j hj, hL1 j hj], ← mul_sum, ← mul_sum,
          sum_kj_zero, mul_zero, mul_zero]
      unfold resid
      rw [hW, sum_sub_distrib, sum_sub_distrib, hs0, hs1]
      unfold qn
      rw [← htdef]
      linarith
    rw [hres]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have := sum_le_card_nsmul (range (d - 1))
      (fun j => |Real.exp (Lj d ε t j 1) - Real.exp (Lj d ε t j 0) -
          Real.exp (Lj d ε t j 0) * Lj1 d ε t j 0|) (6 * ε * ((d : ℝ) - 1) ^ 3 / t)
      (fun j hj => window_taylor hd hε hbig (mem_range.mp hj))
    rw [nsmul_eq_mul, hcard] at this
    refine this.trans (le_of_eq ?_)
    ring
  · push Not at hbig
    refine (resid_crude hd hε n).trans ?_
    rw [← htdef, le_div_iff₀ ht0]
    have h3 : t * t ≤ 6 * ((d : ℝ) - 1) ^ 3 := by
      nlinarith [mul_le_mul hbig.le hbig.le ht0.le (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ε * ((d : ℝ) - 1))]

end Painleve
