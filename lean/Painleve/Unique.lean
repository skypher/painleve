import Painleve.StatementUnique
import Painleve.UniqBounds
import Painleve.Energy

/-!
# Theorem 1.2: uniqueness of the positive solution (Section 7 of `paper.tex`)

Two positive solutions `v, w` of the quartic recurrence give, through
logarithmic means, an exact linear system for `δ_n = log w_n − log v_n`
(`eq:linearized`); the power-weighted energy estimate `energy_core` forces
`δ = 0`.
-/

namespace Painleve

/-- The triple products `T_n = v_n v_{n+1} v_{n+2}`. -/
def tri (v : ℕ → ℝ) (n : ℕ) : ℝ := v n * v (n + 1) * v (n + 2)

theorem log_tri (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (n : ℕ) :
    Real.log (tri v n) = Real.log (v n) + Real.log (v (n + 1)) + Real.log (v (n + 2)) := by
  unfold tri
  rw [Real.log_mul (mul_pos (hv n) (hv (n + 1))).ne' (hv (n + 2)).ne',
    Real.log_mul (hv n).ne' (hv (n + 1)).ne']

theorem tri_pos (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (n : ℕ) : 0 < tri v n := by
  unfold tri; have := hv n; have := hv (n + 1); have := hv (n + 2); positivity

/-- **Theorem 1.2** (`thm:unique`). -/
theorem unique_theorem : Stmt_unique := by
  intro a ha v w hv hw hrv hrw
  set ε : ℝ := 1 / a ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  set K : ℝ := 1 + 6 * ε ^ 2 with hK
  have hK1 : 1 ≤ K := by nlinarith [sq_nonneg ε]
  have hK0 : 0 < K := by linarith
  set c : ℝ := ε / K with hc
  have hc0 : 0 < c := div_pos hε hK0
  have hcε : c ≤ ε := div_le_self hε.le hK1
  set δ : ℕ → ℝ := fun n => Real.log (w n) - Real.log (v n) with hδdef
  set A : ℕ → ℝ := fun n => logMean (v n) (w n) with hA
  set B : ℕ → ℝ := fun n => logMean (tri v n) (tri w n) with hB
  have hlow : ∀ (u : ℕ → ℝ), (∀ n, 0 < u n) → QuarticRec a u → ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ u n := by
    intro u hu hru n
    have := pos_sol_lower a ha u hu hru n
    simpa [hc, hK, hεdef] using this
  have hup : ∀ (u : ℕ → ℝ), (∀ n, 0 < u n) → QuarticRec a u → ∀ n : ℕ,
      u n ≤ ε * ((n : ℝ) + 1) ∧ tri u n ≤ ε * ((n : ℝ) + 1) := by
    intro u hu hru n
    obtain ⟨h1, h2⟩ := pos_sol_upper a ha u hu hru n
    refine ⟨?_, ?_⟩
    · calc u n ≤ ((n : ℝ) + 1) / a ^ 2 := h1
        _ = ε * ((n : ℝ) + 1) := by rw [hεdef]; ring
    · calc tri u n = u n * u (n + 1) * u (n + 2) := rfl
        _ ≤ ((n : ℝ) + 1) / a ^ 2 := h2
        _ = ε * ((n : ℝ) + 1) := by rw [hεdef]; ring
  have hA_low : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ A n := fun n =>
    le_trans (le_min (hlow v hv hrv n) (hlow w hw hrw n)) (min_le_logMean _ _ (hv n) (hw n))
  have hB_pos : ∀ n : ℕ, 0 < B n := fun n =>
    lt_of_lt_of_le (lt_min (tri_pos v hv n) (tri_pos w hw n))
      (min_le_logMean _ _ (tri_pos v hv n) (tri_pos w hw n))
  have hB_up : ∀ n : ℕ, B n ≤ ε * ((n : ℝ) + 1) := fun n =>
    le_trans (logMean_le_max _ _ (tri_pos v hv n) (tri_pos w hw n))
      (max_le (hup v hv hrv n).2 (hup w hw hrw n).2)
  have hδ_bd : ∀ n : ℕ, |δ n| ≤ Real.log K + 2 * Real.log ((n : ℝ) + 1) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have key : ∀ x y : ℝ, c / ((n : ℝ) + 1) ≤ x → x ≤ ε * ((n : ℝ) + 1) →
        c / ((n : ℝ) + 1) ≤ y → y ≤ ε * ((n : ℝ) + 1) →
        Real.log y - Real.log x ≤ Real.log K + 2 * Real.log ((n : ℝ) + 1) := by
      intro x y hx1 hx2 hy1 hy2
      have hx0 : 0 < x := lt_of_lt_of_le (div_pos hc0 hn1) hx1
      have hy0 : 0 < y := lt_of_lt_of_le (div_pos hc0 hn1) hy1
      have h1 : Real.log y ≤ Real.log (ε * ((n : ℝ) + 1)) := Real.log_le_log hy0 hy2
      have h2 : Real.log (c / ((n : ℝ) + 1)) ≤ Real.log x := Real.log_le_log (div_pos hc0 hn1) hx1
      have h3 : Real.log (ε * ((n : ℝ) + 1)) - Real.log (c / ((n : ℝ) + 1)) =
          Real.log K + 2 * Real.log ((n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have : ε * ((n : ℝ) + 1) / (c / ((n : ℝ) + 1)) = K * ((n : ℝ) + 1) ^ 2 := by
          rw [hc]; field_simp
        rw [this, Real.log_mul hK0.ne' (by positivity), Real.log_pow]
        push_cast; ring
      linarith
    rw [abs_le]
    constructor
    · have := key (w n) (v n) (hlow w hw hrw n) (hup w hw hrw n).1 (hlow v hv hrv n) (hup v hv hrv n).1
      simp only [hδdef]; linarith
    · exact key (v n) (w n) (hlow v hv hrv n) (hup v hv hrv n).1 (hlow w hw hrw n) (hup w hw hrw n).1
  -- the exact linear system for δ
  have hdv : ∀ n, w n - v n = A n * δ n := fun n => by
    rw [hA, hδdef]; exact (logMean_mul _ _ (hv n) (hw n)).symm
  have hdT : ∀ n, tri w n - tri v n = B n * (δ n + δ (n + 1) + δ (n + 2)) := fun n => by
    have := logMean_mul _ _ (tri_pos v hv n) (tri_pos w hw n)
    rw [log_tri w hw, log_tri v hv] at this
    rw [hB, hδdef]; simp only; rw [← this]; ring
  have hlin : ∀ n : ℕ, A n * δ n + B n * (δ n + δ (n + 1) + δ (n + 2))
      + (if 1 ≤ n then B (n - 1) * (δ (n - 1) + δ n + δ (n + 1)) else 0)
      + (if 2 ≤ n then B (n - 2) * (δ (n - 2) + δ (n - 1) + δ n) else 0) = 0 := by
    intro n
    have iv := quarticRec_integrated a v hrv n
    have iw := quarticRec_integrated a w hrw n
    rw [← hdv n, ← hdT n]
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | h2
    · simp only [show ¬ (1 ≤ 0) by omega, show ¬ (2 ≤ 0) by omega, if_false] at iv iw ⊢
      unfold tri; linarith
    · simp only [show (1 ≤ 1) by omega, show ¬ (2 ≤ 1) by omega, if_true, if_false] at iv iw ⊢
      have e1 := hdT 0
      unfold tri at e1 ⊢
      simp only [show 1 - 1 = 0 by omega, show 0 + 1 = 1 by omega, show 0 + 2 = 2 by omega,
        show 1 + 1 = 2 by omega] at iv iw e1 ⊢
      rw [← e1]; linarith
    · simp only [show (1 ≤ n) by omega, h2, if_true] at iv iw ⊢
      have e1 := hdT (n - 1)
      have e2 := hdT (n - 2)
      unfold tri at e1 e2 ⊢
      simp only [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega,
        show n - 2 + 1 = n - 1 by omega, show n - 2 + 2 = n by omega] at e1 e2 ⊢
      rw [← e1, ← e2]; linarith
  have hzero := energy_core ε c (Real.log K) hε hc0 hcε δ A B hA_low hB_pos hB_up hδ_bd hlin
  funext n
  have h := hzero n
  simp only [hδdef, sub_eq_zero] at h
  exact (Real.log_injOn_pos (hv n) (hw n) h.symm)

end Painleve
