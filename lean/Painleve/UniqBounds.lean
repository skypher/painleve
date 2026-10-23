import Painleve.Statement

namespace Painleve

/-- The logarithmic mean. -/
noncomputable def logMean (x y : ℝ) : ℝ := if x = y then x else (y - x) / (Real.log y - Real.log x)

lemma log_sub_ne_zero (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    Real.log y - Real.log x ≠ 0 := by
  intro h
  apply hxy
  exact Real.log_injOn_pos (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) (by linarith)

theorem logMean_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    logMean x y * (Real.log y - Real.log x) = y - x := by
  unfold logMean
  split_ifs with h
  · subst h
    simp
  · rw [div_mul_cancel₀]
    exact log_sub_ne_zero x y hx hy h

/-- Bounds for `x < y`. -/
lemma logMean_bounds_lt (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    x ≤ logMean x y ∧ logMean x y ≤ y := by
  have hy : 0 < y := lt_trans hx hxy
  have hL : 0 < Real.log y - Real.log x := by
    have := Real.log_lt_log hx hxy
    linarith
  have hne : x ≠ y := ne_of_lt hxy
  have hM : logMean x y = (y - x) / (Real.log y - Real.log x) := if_neg hne
  rw [hM]
  have hq : 0 < y / x := div_pos hy hx
  have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos hq
  have h2 : 1 - (y / x)⁻¹ ≤ Real.log (y / x) := Real.one_sub_inv_le_log_of_pos hq
  rw [Real.log_div hy.ne' hx.ne'] at h1 h2
  constructor
  · rw [le_div_iff₀ hL]
    have : x * (y / x - 1) = y - x := by field_simp
    have hx' : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) :=
      mul_le_mul_of_nonneg_left h1 hx.le
    linarith
  · rw [div_le_iff₀ hL]
    have : y * (1 - (y / x)⁻¹) = y - x := by field_simp
    have hy' : y * (1 - (y / x)⁻¹) ≤ y * (Real.log y - Real.log x) :=
      mul_le_mul_of_nonneg_left h2 hy.le
    linarith

lemma logMean_comm (x y : ℝ) : logMean x y = logMean y x := by
  unfold logMean
  by_cases h : x = y
  · subst h
    simp
  · have e : (x - y) / (Real.log x - Real.log y) = (y - x) / (Real.log y - Real.log x) := by
      rw [show x - y = -(y - x) by ring, show Real.log x - Real.log y = -(Real.log y - Real.log x) by ring,
        neg_div_neg_eq]
    rw [if_neg h, if_neg (Ne.symm h), e]

theorem min_le_logMean (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : min x y ≤ logMean x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [min_eq_left h.le]
    exact (logMean_bounds_lt x y hx h).1
  · subst h
    unfold logMean
    simp
  · rw [min_eq_right h.le, logMean_comm]
    exact (logMean_bounds_lt y x hy h).1

theorem logMean_le_max (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : logMean x y ≤ max x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [max_eq_right h.le]
    exact (logMean_bounds_lt x y hx h).2
  · subst h
    unfold logMean
    simp
  · rw [max_eq_left h.le, logMean_comm]
    exact (logMean_bounds_lt y x hy h).2

/-! ### Integrated form of the recurrence -/

lemma extZ_of_neg (v : ℕ → ℝ) {k : ℤ} (hk : k < 0) : extZ v k = 0 := by
  unfold extZ
  rw [if_pos hk]

lemma extZ_of_nat (v : ℕ → ℝ) (k : ℕ) : extZ v (k : ℤ) = v k := by
  unfold extZ
  rw [if_neg (by omega)]
  simp

theorem quarticRec_integrated (a : ℝ) (v : ℕ → ℝ) (hv : QuarticRec a v) (n : ℕ) :
    v n + v n * v (n + 1) * v (n + 2)
      + (if 1 ≤ n then v (n - 1) * v n * v (n + 1) else 0)
      + (if 2 ≤ n then v (n - 2) * v (n - 1) * v n else 0) = ((n : ℝ) + 1) / a ^ 2 := by
  have h := hv n
  rcases n with _ | _ | m
  · have e1 : ((0 : ℕ) : ℤ) - 1 < 0 := by norm_num
    have e2 : ((0 : ℕ) : ℤ) - 2 < 0 := by norm_num
    rw [extZ_of_neg v e1, extZ_of_neg v e2] at h
    simp only [if_neg (show ¬ 1 ≤ 0 by omega), if_neg (show ¬ 2 ≤ 0 by omega)]
    linear_combination h
  · have e1 : ((0 + 1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) := by norm_num
    have e2 : ((0 + 1 : ℕ) : ℤ) - 2 < 0 := by norm_num
    rw [e1, extZ_of_nat, extZ_of_neg v e2] at h
    simp only [if_pos (show 1 ≤ 0 + 1 by omega), if_neg (show ¬ 2 ≤ 0 + 1 by omega)]
    simp only [zero_add] at *
    linear_combination h
  · have e1 : ((m + 1 + 1 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((m + 1 + 1 : ℕ) : ℤ) - 2 = ((m : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, extZ_of_nat, extZ_of_nat] at h
    simp only [if_pos (show 1 ≤ m + 1 + 1 by omega), if_pos (show 2 ≤ m + 1 + 1 by omega)]
    have e3 : m + 1 + 1 - 1 = m + 1 := by omega
    have e4 : m + 1 + 1 - 2 = m := by omega
    rw [e3, e4]
    push_cast at h ⊢
    linear_combination h

theorem pos_sol_upper (a : ℝ) (ha : 0 < a) (v : ℕ → ℝ) (hpos : ∀ n, 0 < v n) (hv : QuarticRec a v)
    (n : ℕ) : v n ≤ ((n : ℝ) + 1) / a ^ 2 ∧ v n * v (n + 1) * v (n + 2) ≤ ((n : ℝ) + 1) / a ^ 2 := by
  have hint := quarticRec_integrated a v hv n
  have h1 : 0 < v n := hpos n
  have h2 : 0 < v n * v (n + 1) * v (n + 2) := mul_pos (mul_pos h1 (hpos _)) (hpos _)
  have h3 : 0 ≤ (if 1 ≤ n then v (n - 1) * v n * v (n + 1) else 0) := by
    split_ifs
    · exact (mul_pos (mul_pos (hpos _) h1) (hpos _)).le
    · exact le_refl _
  have h4 : 0 ≤ (if 2 ≤ n then v (n - 2) * v (n - 1) * v n else 0) := by
    split_ifs
    · exact (mul_pos (mul_pos (hpos _) (hpos _)) h1).le
    · exact le_refl _
  constructor <;> linarith

/-- Bound on the bracket `extZ`-part of the recurrence. -/
lemma X_bound (e : ℝ) (v : ℕ → ℝ) (hpos : ∀ k, 0 < v k)
    (hU : ∀ k : ℕ, v k ≤ e * ((k : ℝ) + 1)) (he : 0 ≤ e) (n : ℕ) :
    extZ v ((n : ℤ) - 1) * extZ v ((n : ℤ) - 2) + v (n + 1) * extZ v ((n : ℤ) - 1)
      + v (n + 2) * v (n + 1) ≤ e ^ 2 * (3 * (n : ℝ) ^ 2 + 6 * (n : ℝ) + 6) := by
  rcases n with _ | _ | m
  · have e1 : ((0 : ℕ) : ℤ) - 1 < 0 := by norm_num
    have e2 : ((0 : ℕ) : ℤ) - 2 < 0 := by norm_num
    rw [extZ_of_neg v e1, extZ_of_neg v e2]
    have b1 := hU 1
    have b2 := hU 2
    norm_num at b1 b2 ⊢
    have t := mul_le_mul b2 b1 (hpos 1).le (mul_nonneg he (by norm_num))
    nlinarith [t]
  · have e1 : ((0 + 1 : ℕ) : ℤ) - 1 = ((0 : ℕ) : ℤ) := by norm_num
    have e2 : ((0 + 1 : ℕ) : ℤ) - 2 < 0 := by norm_num
    rw [e1, extZ_of_nat, extZ_of_neg v e2]
    have b0 := hU 0
    have b2 := hU (0 + 1 + 1)
    have b3 := hU (0 + 1 + 2)
    have t1 := mul_le_mul b2 b0 (hpos 0).le (mul_nonneg he (by positivity))
    have t2 := mul_le_mul b3 b2 (hpos _).le (mul_nonneg he (by positivity))
    norm_num at b0 b2 b3 t1 t2 ⊢
    nlinarith [t1, t2]
  · have e1 : ((m + 1 + 1 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((m + 1 + 1 : ℕ) : ℤ) - 2 = ((m : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, extZ_of_nat, extZ_of_nat]
    have t1 := mul_le_mul (hU (m + 1)) (hU m) (hpos m).le (mul_nonneg he (by positivity))
    have t2 := mul_le_mul (hU (m + 1 + 1 + 1)) (hU (m + 1)) (hpos _).le
      (mul_nonneg he (by positivity))
    have t3 := mul_le_mul (hU (m + 1 + 1 + 2)) (hU (m + 1 + 1 + 1)) (hpos _).le
      (mul_nonneg he (by positivity))
    push_cast at t1 t2 t3 ⊢
    nlinarith [t1, t2, t3]

theorem pos_sol_lower (a : ℝ) (ha : 0 < a) (v : ℕ → ℝ) (hpos : ∀ n, 0 < v n) (hv : QuarticRec a v)
    (n : ℕ) : (1 / a ^ 2) / (1 + 6 * (1 / a ^ 2) ^ 2) / ((n : ℝ) + 1) ≤ v n := by
  obtain ⟨e, he_eq⟩ : ∃ e : ℝ, e = 1 / a ^ 2 := ⟨_, rfl⟩
  rw [← he_eq]
  have he : 0 < e := by rw [he_eq]; positivity
  have hU : ∀ k : ℕ, v k ≤ e * ((k : ℝ) + 1) := by
    intro k
    calc v k ≤ ((k : ℝ) + 1) / a ^ 2 := (pos_sol_upper a ha v hpos hv k).1
      _ = e * ((k : ℝ) + 1) := by rw [he_eq]; ring
  have hR : ((n : ℝ) + 1) / a ^ 2 = e * ((n : ℝ) + 1) := by rw [he_eq]; ring
  have hE := hv n
  rw [hR] at hE
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = extZ v ((n : ℤ) - 1) * extZ v ((n : ℤ) - 2)
      + v (n + 1) * extZ v ((n : ℤ) - 1) + v (n + 2) * v (n + 1) := ⟨_, rfl⟩
  have hX := X_bound e v hpos hU he.le n
  rw [← hXd] at hX
  have hE' : v n * (1 + X) = e * ((n : ℝ) + 1) := by
    rw [hXd, ← hE]
    ring
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  have hBpos : 0 < 1 + X := by
    have h1 : 0 < v n * (1 + X) := by
      rw [hE']
      exact mul_pos he hNpos
    exact pos_of_mul_pos_right h1 (hpos n).le
  have hd : 0 ≤ ((n : ℝ) ^ 2 + 2 * (n : ℝ)) * (1 + 3 * e ^ 2) := by positivity
  have hBle : 1 + X ≤ (1 + 6 * e ^ 2) * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [hX, hd]
  have hmul : v n * (1 + X) ≤ v n * ((1 + 6 * e ^ 2) * ((n : ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hBle (hpos n).le
  have hK : (0 : ℝ) < 1 + 6 * e ^ 2 := by positivity
  rw [div_div, div_le_iff₀ (mul_pos hK hNpos)]
  have h3 : e * ((n : ℝ) + 1) ≤ (v n * ((1 + 6 * e ^ 2) * ((n : ℝ) + 1))) * ((n : ℝ) + 1) := by
    calc e * ((n : ℝ) + 1) = v n * (1 + X) := hE'.symm
      _ ≤ v n * ((1 + 6 * e ^ 2) * ((n : ℝ) + 1) ^ 2) := hmul
      _ = (v n * ((1 + 6 * e ^ 2) * ((n : ℝ) + 1))) * ((n : ℝ) + 1) := by ring
  exact le_of_mul_le_mul_right h3 hNpos

end Painleve
