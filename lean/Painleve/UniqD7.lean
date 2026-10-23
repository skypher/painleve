import Painleve.UniqD6

/-!
# Proposition 8.3 (`prop:apriori`): the a priori bound and the asymptotics

For every positive solution `v` of `eq:general-recurrence` (`d ≥ 3`, `ε > 0`),
`δ_n = log(v_n/q_n)` is square summable; hence `v_n/q_n → 1` and
`v_n ((d-1)/(ε(n+1)))^{1/(d-1)} → 1`.
-/

open Finset Filter Topology

namespace Painleve

variable {d : ℕ}

/-! ### Bounds for the approximate solution -/

lemma gfun_le_iff {x y : ℝ} : gfun d x ≤ gfun d y ↔ x ≤ y := gfun_strictMono.le_iff_le

lemma qapp_ge_of_gfun_le {ε t x : ℝ} (h : gfun d x ≤ ε * t) : x ≤ qapp d ε t := by
  rw [← gfun_le_iff (d := d), gfun_qapp]; exact h

/-- `q(1) ≥ ε/K`. -/
lemma qapp_one_ge (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) : ε / Kc d ε ≤ qapp d ε 1 := by
  apply qapp_ge_of_gfun_le
  have hK := Kc_pos hd hε
  have hK1 : 1 ≤ Kc d ε := by
    unfold Kc
    have : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have : 0 ≤ ((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2) := by positivity
    linarith
  unfold gfun
  rw [max_eq_left (by positivity), Nat.cast_sub (by omega), Nat.cast_one, mul_one]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- `(d-1)(ε/K)^{d-1} ≤ ε - ε/K`, i.e. `(d-1) ε^{d-2} ≤ K^{d-2} (K - 1) = K^{d-2} (d-1)^{d-1} ε^{d-2}`
  have hpow : (ε / Kc d ε) ^ (d - 1) = ε * ε ^ (d - 2) / (Kc d ε * Kc d ε ^ (d - 2)) := by
    rw [div_pow, ← pow_succ', ← pow_succ', show d - 2 + 1 = d - 1 by omega]
  rw [hpow]
  have hKd : 1 ≤ Kc d ε ^ (d - 2) := one_le_pow₀ hK1
  have hdd : (d : ℝ) - 1 ≤ ((d : ℝ) - 1) ^ (d - 1) := by
    calc (d : ℝ) - 1 = ((d : ℝ) - 1) ^ 1 := (pow_one _).symm
      _ ≤ ((d : ℝ) - 1) ^ (d - 1) := pow_le_pow_right₀ hd1 (by omega)
  have hKm : Kc d ε - 1 = ((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2) := by unfold Kc; ring
  have hεp : 0 < ε ^ (d - 2) := by positivity
  have hP : 0 < Kc d ε ^ (d - 2) := by positivity
  have e : ε / Kc d ε + ((d : ℝ) - 1) * (ε * ε ^ (d - 2) / (Kc d ε * Kc d ε ^ (d - 2)))
      = ε * (Kc d ε ^ (d - 2) + ((d : ℝ) - 1) * ε ^ (d - 2)) / (Kc d ε * Kc d ε ^ (d - 2)) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  -- `P + (d-1) E ≤ K P` since `K P - P = P (d-1)^{d-1} E ≥ (d-1) E`
  have h1 : ((d : ℝ) - 1) * ε ^ (d - 2) ≤ Kc d ε ^ (d - 2) * (((d : ℝ) - 1) ^ (d - 1) * ε ^ (d - 2)) := by
    have := mul_le_mul hKd (mul_le_mul_of_nonneg_right hdd hεp.le) (by positivity) (by positivity)
    linarith
  have h2 : Kc d ε ^ (d - 2) + ((d : ℝ) - 1) * ε ^ (d - 2) ≤ Kc d ε * Kc d ε ^ (d - 2) := by
    rw [← hKm] at h1; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]

/-- `q(t) ≥ q(1) t^{1/(d-1)}` for `t ≥ 1`. -/
lemma qapp_lower (hd : 2 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t) :
    qapp d ε 1 * t ^ (1 / ((d : ℝ) - 1)) ≤ qapp d ε t := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq1 := qapp_pos (d := d) hε one_pos
  have heq1 := qapp_eq (d := d) (by omega) hε one_pos
  have ht0 : 0 < t := by linarith
  apply qapp_ge_of_gfun_le
  have hx0 : 0 ≤ qapp d ε 1 * t ^ (1 / ((d : ℝ) - 1)) := by positivity
  unfold gfun
  rw [max_eq_left hx0, Nat.cast_sub (by omega), Nat.cast_one]
  have hroot : (t ^ (1 / ((d : ℝ) - 1))) ^ (d - 1) = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, Nat.cast_sub (by omega), Nat.cast_one,
      one_div_mul_cancel (by linarith), Real.rpow_one]
  have hle : t ^ (1 / ((d : ℝ) - 1)) ≤ t := by
    calc t ^ (1 / ((d : ℝ) - 1)) ≤ t ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht (by rw [div_le_one (by linarith)]; linarith)
      _ = t := Real.rpow_one t
  rw [mul_pow, hroot]
  nlinarith [mul_le_mul_of_nonneg_left hle hq1.le]

/-- `q(t) ≤ (εt/(d-1))^{1/(d-1)}`. -/
lemma qapp_upper (hd : 2 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    qapp d ε t ≤ (ε * t / ((d : ℝ) - 1)) ^ (1 / ((d : ℝ) - 1)) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq := qapp_pos (d := d) hε ht
  have hpow := qapp_pow_le hd hε ht
  have h1 : qapp d ε t ^ (d - 1) ≤ ε * t / ((d : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hroot : (qapp d ε t ^ (d - 1)) ^ (1 / ((d : ℝ) - 1)) = qapp d ε t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Nat.cast_sub (by omega), Nat.cast_one,
      mul_one_div_cancel (by linarith), Real.rpow_one]
  calc qapp d ε t = (qapp d ε t ^ (d - 1)) ^ (1 / ((d : ℝ) - 1)) := hroot.symm
    _ ≤ (ε * t / ((d : ℝ) - 1)) ^ (1 / ((d : ℝ) - 1)) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-! ### The linearized system for a positive solution -/

/-- `δ_n = log v_n - log q_n`. -/
noncomputable def devD (d : ℕ) (ε : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (v n) - Real.log (qn d ε n)

lemma log_Tw {v : ℕ → ℝ} (hv : ∀ n, 0 < v n) (m : ℕ) :
    Real.log (Tw d v m) = ∑ i ∈ range (d - 1), Real.log (v (m + i)) := by
  unfold Tw
  exact Real.log_prod (fun i _ => (hv _).ne')

/-- `eq:linearized`: `a_n δ_n + ∑_m b_m D_m = -r_n`. -/
theorem linearized_sol (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hrec : GenRec d ε v) (n : ℕ) :
    logMean (qn d ε n) (v n) * devD d ε v n + ∑ j ∈ range (d - 1),
      (if j ≤ n then logMean (Tw d (qn d ε) (n - j)) (Tw d v (n - j)) *
        ∑ i ∈ range (d - 1), devD d ε v (n - j + i) else 0) = -resid d ε n := by
  have hq : ∀ m, 0 < qn d ε m := qn_pos hε
  have h1 : logMean (qn d ε n) (v n) * devD d ε v n = v n - qn d ε n :=
    logMean_mul _ _ (hq n) (hv n)
  have h2 : ∀ m, logMean (Tw d (qn d ε) m) (Tw d v m) * ∑ i ∈ range (d - 1), devD d ε v (m + i)
      = Tw d v m - Tw d (qn d ε) m := by
    intro m
    have := logMean_mul _ _ (Tw_pos (d := d) hq m) (Tw_pos (d := d) hv m)
    rw [log_Tw hv, log_Tw hq, ← sum_sub_distrib] at this
    exact this
  have hrecn := (genRec_iff ε v).mp hrec n
  rw [h1]
  have hW : ∑ j ∈ range (d - 1), (if j ≤ n then logMean (Tw d (qn d ε) (n - j)) (Tw d v (n - j)) *
        ∑ i ∈ range (d - 1), devD d ε v (n - j + i) else 0)
      = Wsum d v n - Wsum d (qn d ε) n := by
    unfold Wsum
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs
    · exact h2 (n - j)
    · ring
  rw [hW]
  unfold resid
  linarith

/-- `|δ_n| ≤ log K + (d-2) log(n+1)`. -/
theorem devD_bound (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hrec : GenRec d ε v) (n : ℕ) :
    |devD d ε v n| ≤ Real.log (Kc d ε) + ((d : ℝ) - 2) * Real.log ((n : ℝ) + 1) := by
  have hd2 : 2 ≤ d := by omega
  have hK := Kc_pos hd2 hε
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1' : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  set lo : ℝ := ε / Kc d ε * ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) with hlo
  set hi : ℝ := ((n : ℝ) + 1) * ε with hhi
  have hlo0 : 0 < lo := by positivity
  -- both `v_n` and `q_n` lie in `[lo, hi]`
  have hv1 : lo ≤ v n := crude_lower hd hε hv hrec n
  have hv2 : v n ≤ hi := (crude_upper hd2 hv hrec n).1
  have hq2 : qn d ε n ≤ hi := by
    unfold qn; rw [hhi, mul_comm]; exact qapp_le (by omega) hε hn1
  have hq1 : lo ≤ qn d ε n := by
    have h1 : ε / Kc d ε ≤ qapp d ε 1 := qapp_one_ge hd2 hε
    have h2 : qapp d ε 1 ≤ qn d ε n := qapp_mono hε hn1'
    have h3 : ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1' (by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    have : lo ≤ ε / Kc d ε := by
      rw [hlo]; exact mul_le_of_le_one_right (by positivity) h3
    linarith
  have hspan : Real.log hi - Real.log lo = Real.log (Kc d ε) + ((d : ℝ) - 2) * Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hlo0.ne', hhi, hlo]
    have : ((n : ℝ) + 1) * ε / (ε / Kc d ε * ((n : ℝ) + 1) ^ (-((d : ℝ) - 3)))
        = Kc d ε * ((n : ℝ) + 1) ^ ((d : ℝ) - 2) := by
      rw [Real.rpow_neg hn1.le]
      have e : ((n : ℝ) + 1) ^ ((d : ℝ) - 2) = ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ ((d : ℝ) - 3) := by
        rw [show (d : ℝ) - 2 = 1 + ((d : ℝ) - 3) by ring, Real.rpow_add hn1, Real.rpow_one]
      rw [e]
      have : 0 < ((n : ℝ) + 1) ^ ((d : ℝ) - 3) := by positivity
      field_simp
    rw [this, Real.log_mul hK.ne' (by positivity), Real.log_rpow hn1]
  unfold devD
  rw [abs_le]
  constructor
  · have := Real.log_le_log hlo0 hv1
    have := Real.log_le_log (lt_of_lt_of_le hlo0 hq1) hq2
    linarith
  · have := Real.log_le_log (lt_of_lt_of_le hlo0 hv1) hv2
    have := Real.log_le_log hlo0 hq1
    linarith

/-- **Proposition 8.3** (`prop:apriori`): `∑ δ_n² < ∞`. -/
theorem apriori (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hrec : GenRec d ε v) : Summable (fun n => devD d ε v n ^ 2) := by
  have hd2 : 2 ≤ d := by omega
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set L := d - 1 with hLdef
  have hL : 1 ≤ L := by omega
  have hLr : ((L : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [hLdef, Nat.cast_sub (by omega)]; norm_num
  set p : ℝ := 1 / (4 * ((d : ℝ) - 1)) with hpdef
  have hp0 : 0 < p := by
    rw [hpdef]
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one (by linarith)]; linarith
  set δ := devD d ε v with hδdef
  set a : ℕ → ℝ := fun n => logMean (qn d ε n) (v n) with hadef
  set b : ℕ → ℝ := fun m => logMean (Tw d (qn d ε) m) (Tw d v m) with hbdef
  set r : ℕ → ℝ := fun n => resid d ε n with hrdef
  have hq : ∀ m, 0 < qn d ε m := qn_pos hε
  have hK := Kc_pos hd2 hε
  set H : ℝ → ℝ := fun t => Real.log (Kc d ε) + ((d : ℝ) - 2) * Real.log t with hH
  have hδb : ∀ n, |δ n| ≤ Real.log (Kc d ε) + ((d : ℝ) - 2) * Real.log ((n : ℝ) + 1) :=
    devD_bound hd hε hv hrec
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    (lt_of_lt_of_le (lt_min (hq n) (hv n)) (min_le_logMean _ _ (hq n) (hv n))).le
  have hb0 : ∀ m, 0 ≤ b m := fun m =>
    (lt_of_lt_of_le (lt_min (Tw_pos hq m) (Tw_pos hv m))
      (min_le_logMean _ _ (Tw_pos hq m) (Tw_pos hv m))).le
  have hb : ∀ m, b m ≤ ε * ((m : ℝ) + 1) := fun m => by
    refine (logMean_le_max _ _ (Tw_pos hq m) (Tw_pos hv m)).trans (max_le ?_ ?_)
    · rw [mul_comm]; exact Qm_le hd2 hε m
    · rw [mul_comm]; exact (crude_upper hd2 hv hrec m).2
  have hlin := linearized_sol hd2 hε hv hrec
  -- summability of the source term
  set CH : ℝ := |Real.log (Kc d ε)| + ((d : ℝ) - 2) * (2 / p) with hCH
  have hδC : ∀ n, |δ n| ≤ CH * ((n : ℝ) + 1) ^ (p / 2) := by
    intro n
    have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    have hxp : 1 ≤ ((n : ℝ) + 1) ^ (p / 2) := Real.one_le_rpow hx1 (by positivity)
    have hlog := log_le_rpow_half hx1 hp0
    refine (hδb n).trans ?_
    have h2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
    have : ((d : ℝ) - 2) * Real.log ((n : ℝ) + 1) ≤ ((d : ℝ) - 2) * (2 / p * ((n : ℝ) + 1) ^ (p / 2)) :=
      mul_le_mul_of_nonneg_left hlog h2
    have h3 := le_abs_self (Real.log (Kc d ε))
    have h4 : 0 ≤ |Real.log (Kc d ε)| := abs_nonneg _
    rw [hCH]
    nlinarith
  have hS1 : Summable (fun n : ℕ => |r n| * (((n : ℝ) + 1) ^ (-p)) ^ 2 * |δ n|) := by
    have hs := summable_shift_rpow (1 + 3 * p / 2) (by linarith)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hs.mul_left (6 * ε * ((d : ℝ) - 1) ^ 4 * CH))
    set x : ℝ := (n : ℝ) + 1 with hx
    have hx0 : 0 < x := by positivity
    have hr := resid_bound hd2 hε n
    have hrx : |r n| ≤ 6 * ε * ((d : ℝ) - 1) ^ 4 * x⁻¹ := by
      simp only [hrdef]; rw [← div_eq_mul_inv]; exact hr
    have hw2 : (x ^ (-p)) ^ 2 = x ^ (-(2 * p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
    have hexp : x⁻¹ * x ^ (-(2 * p)) * x ^ (p / 2) = x ^ (-(1 + 3 * p / 2)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have hw0 : 0 ≤ (x ^ (-p)) ^ 2 := sq_nonneg _
    have hCH0 : 0 ≤ CH := by
      rw [hCH]
      have : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
      positivity
    calc |r n| * (x ^ (-p)) ^ 2 * |δ n|
        ≤ (6 * ε * ((d : ℝ) - 1) ^ 4 * x⁻¹) * (x ^ (-p)) ^ 2 * (CH * x ^ (p / 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hrx hw0) (hδC n) (abs_nonneg _)
          have : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
          positivity
      _ = 6 * ε * ((d : ℝ) - 1) ^ 4 * CH * (x⁻¹ * x ^ (-(2 * p)) * x ^ (p / 2)) := by
          rw [hw2]; ring
      _ = 6 * ε * ((d : ℝ) - 1) ^ 4 * CH * x ^ (-(1 + 3 * p / 2)) := by rw [hexp]
  have hgs : Summable (fun n : ℕ => δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))) :=
    summable_gD (Real.log (Kc d ε)) ((d : ℝ) - 2) p (by linarith) hp0 δ hδb
  have hE := energy_weighted L hL p ε hp0 hp1 hε a b δ r ha0 hb0 hb
    (fun n => by simpa [hadef, hbdef, hδdef, hrdef, hLdef] using hlin n) hS1 hgs
  set B := (∑' n, |r n| * (((n : ℝ) + 1) ^ (-p)) ^ 2 * |δ n|) +
    ε * p ^ 2 * ((L : ℝ) - 1) ^ 2 * L / 2 * (L * (L : ℝ) ^ (1 + 2 * p) *
      ∑' n, δ n ^ 2 * ((n : ℝ) + 1) ^ (-(1 + 2 * p))) with hB
  -- the lower bound `a_n w_n² ≥ q(1)/G`
  set c : ℝ := 1 / (2 * ((d : ℝ) - 1)) with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity
  have h2p : 2 * p = c := by rw [hpdef, hcdef]; field_simp; ring
  set G : ℝ := 1 + |Real.log (Kc d ε)| + ((d : ℝ) - 2) / c with hG
  have hG0 : 0 < G := by
    rw [hG]
    have : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
    positivity
  have hq1 := qapp_pos (d := d) hε one_pos
  set c0 : ℝ := qapp d ε 1 / G with hc0def
  have hc00 : 0 < c0 := div_pos hq1 hG0
  have hlow : ∀ n, c0 ≤ a n * (((n : ℝ) + 1) ^ (-p)) ^ 2 := by
    intro n
    set x : ℝ := (n : ℝ) + 1 with hx
    have hx1 : 1 ≤ x := by rw [hx]; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    have hx0 : 0 < x := by linarith
    have hxc : 1 ≤ x ^ c := Real.one_le_rpow hx1 hc0.le
    -- `a_n ≥ q_n/(1 + |δ_n|)`
    have h1 : qn d ε n / (1 + |δ n|) ≤ a n := by
      have := logMean_lower (hq n) (hv n)
      simpa [hadef, hδdef, devD] using this
    -- `q_n ≥ q(1) x^{2c}`
    have h2 : qapp d ε 1 * x ^ (2 * c) ≤ qn d ε n := by
      have := qapp_lower hd2 hε hx1
      rw [show (1 / ((d : ℝ) - 1)) = 2 * c by rw [hcdef]; field_simp] at this
      simpa [qn, hx] using this
    -- `1 + |δ_n| ≤ G x^c`
    have h3 : 1 + |δ n| ≤ G * x ^ c := by
      have hlog : Real.log x ≤ x ^ c / c := Real.log_le_rpow_div hx0.le hc0
      have hb' := hδb n
      rw [← hx] at hb'
      have h4 : ((d : ℝ) - 2) * Real.log x ≤ ((d : ℝ) - 2) * (x ^ c / c) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      have h5 := le_abs_self (Real.log (Kc d ε))
      have h6 : 0 ≤ |Real.log (Kc d ε)| := abs_nonneg _
      rw [hG]
      have h7 : ((d : ℝ) - 2) * (x ^ c / c) = ((d : ℝ) - 2) / c * x ^ c := by ring
      nlinarith
    have hw2 : (x ^ (-p)) ^ 2 = (x ^ c)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg hx0.le]
      congr 1; push_cast; linarith
    have hx2c : x ^ (2 * c) = x ^ c * x ^ c := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hxc0 : 0 < x ^ c := by positivity
    have hden : 0 < 1 + |δ n| := by positivity
    rw [hw2, hc0def]
    calc qapp d ε 1 / G = qapp d ε 1 * x ^ (2 * c) / (G * x ^ c) * (x ^ c)⁻¹ := by
          rw [hx2c]; field_simp
      _ ≤ qn d ε n / (1 + |δ n|) * (x ^ c)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div₀ (hq n).le h2 hden h3
      _ ≤ a n * (x ^ c)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
  refine summable_of_sum_range_le (c := B / c0) (fun n => sq_nonneg _) fun N => ?_
  rw [le_div_iff₀ hc00]
  refine le_trans ?_ (hE N)
  rw [sum_mul]
  refine sum_le_sum fun n _ => ?_
  have := mul_le_mul_of_nonneg_left (hlow n) (sq_nonneg (δ n))
  nlinarith

end Painleve
