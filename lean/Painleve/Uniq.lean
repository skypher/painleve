import Painleve.Statement
namespace Painleve

lemma extZ_congr (v w : ℕ → ℝ) (m : ℕ) (h : ∀ j, j ≤ m → v j = w j) (k : ℤ) (hk : k ≤ (m : ℤ)) :
    extZ v k = extZ w k := by
  unfold extZ
  split_ifs
  · rfl
  · exact h _ (by omega)

theorem quarticRec_unique (a : ℝ) (v w : ℕ → ℝ) (hv : QuarticRec a v) (hw : QuarticRec a w)
    (h0 : v 0 = w 0) (h1 : v 1 = w 1) (hpos : ∀ n, 0 < v n) : v = w := by
  have step : ∀ k : ℕ, (∀ j, j ≤ k + 1 → v j = w j) → v (k + 2) = w (k + 2) := by
    intro k hk
    have ev := hv k
    have ew := hw k
    have e1 : extZ v ((k : ℤ) - 1) = extZ w ((k : ℤ) - 1) :=
      extZ_congr v w (k + 1) hk _ (by omega)
    have e2 : extZ v ((k : ℤ) - 2) = extZ w ((k : ℤ) - 2) :=
      extZ_congr v w (k + 1) hk _ (by omega)
    have hk0 : v k = w k := hk k (by omega)
    have hk1 : v (k + 1) = w (k + 1) := hk (k + 1) (le_refl _)
    have hw0 : 0 < w k := by rw [← hk0]; exact hpos k
    have hw1 : 0 < w (k + 1) := by rw [← hk1]; exact hpos (k + 1)
    rw [e1, e2, hk0, hk1] at ev
    have hprod : w k * w (k + 1) * (v (k + 2) - w (k + 2)) = 0 := by
      linear_combination ev - ew
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h (mul_pos hw0 hw1).ne'
    · linarith
  have key : ∀ m : ℕ, ∀ j, j ≤ m + 1 → v j = w j := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact h0
      · exact h1
    | succ k ih =>
      intro j hj
      rcases (by omega : j ≤ k + 1 ∨ j = k + 2) with h | rfl
      · exact ih j (by omega)
      · exact step k ih
  funext j
  exact key j j (by omega)

end Painleve
