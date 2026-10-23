import Painleve.UniqD8
import Painleve.MainD
import Painleve.Main
import Painleve.Unique

/-!
# Theorem 1.3 (`thm:unique`)

For `d ≥ 3` and `ε > 0`, every positive solution of `eq:general-recurrence`
satisfies `v_n ((d-1)/(ε(n+1)))^{1/(d-1)} → 1`, and there is at most one.
With `V_n = a^{2/(d-2)} v_n` and `ε = a^{-d/(d-2)}`, `eq:FH-recurrence` becomes
`eq:general-recurrence`; so `V_n = 𝔥_{n+1}/𝔥_n` (Theorem 1.1(ii)) is the unique
positive solution of `eq:FH-recurrence`, and for `d = 4` the Bessel solution of
Theorem 1.2 is the unique positive solution of the quartic recurrence.
-/

open Finset Filter Topology

namespace Painleve

variable {d : ℕ}

lemma extZ_div (W : ℕ → ℝ) (c : ℝ) (t : ℤ) : extZ (fun n => W n / c) t = extZ W t / c := by
  unfold extZ; split_ifs <;> simp

/-- Reflecting both window indices: `∑_j ∏_k V_{n+j-k} = ∑_j ∏_i V_{n-j+i}`. -/
lemma window_reflect (W : ℕ → ℝ) (L n : ℕ) :
    ∑ j ∈ range L, ∏ k ∈ range L, extZ W ((n : ℤ) + j - k)
      = ∑ j ∈ range L, ∏ i ∈ range L, extZ W ((n : ℤ) - j + i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [← prod_range_reflect]
  refine prod_congr rfl fun k hk => ?_
  have hj' := mem_range.mp hj
  have hk' := mem_range.mp hk
  congr 1
  push_cast [Nat.cast_sub (show 1 ≤ L by omega), Nat.cast_sub (show j ≤ L - 1 by omega),
    Nat.cast_sub (show k ≤ L - 1 by omega)]
  ring

/-- The normalization `V = a^{2/(d-2)} v`, `ε = a^{-d/(d-2)}`. -/
theorem fhrec_to_genRec (hd : 3 ≤ d) {a : ℝ} (ha : 0 < a) {W : ℕ → ℝ} (hW : FHRec d a W) :
    GenRec d (a ^ (-(d : ℝ) / ((d : ℝ) - 2))) (fun n => W n / a ^ ((2 : ℝ) / ((d : ℝ) - 2))) := by
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  set c : ℝ := a ^ ((2 : ℝ) / ((d : ℝ) - 2)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos ha _
  have hcd : c ^ (d - 2) = a ^ 2 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, Nat.cast_sub (by omega)]
    rw [show (2 : ℝ) / ((d : ℝ) - 2) * ((d : ℝ) - (2 : ℕ)) = 2 by push_cast; field_simp]
    exact Real.rpow_two a
  have hεc : a ^ (-(d : ℝ) / ((d : ℝ) - 2)) * c = a⁻¹ := by
    rw [hc, ← Real.rpow_add ha, ← Real.rpow_neg_one]
    congr 1; field_simp; ring
  have hcd1 : c ^ (d - 1) = a ^ 2 * c := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ, hcd]
  intro n
  have h := hW n
  rw [window_reflect W (d - 1) n] at h
  have hprod : ∀ j ∈ range (d - 1), ∏ i ∈ range (d - 1), extZ (fun n => W n / c) ((n : ℤ) - j + i)
      = (∏ i ∈ range (d - 1), extZ W ((n : ℤ) - j + i)) / c ^ (d - 1) := by
    intro j _
    simp_rw [extZ_div]
    rw [prod_div_distrib, prod_const, card_range]
  rw [sum_congr rfl hprod, ← sum_div, hcd1]
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hε : a ^ (-(d : ℝ) / ((d : ℝ) - 2)) = a⁻¹ / c := by
    rw [← hεc]; field_simp
  rw [hε]
  field_simp
  field_simp at h
  linarith

/-- **Theorem 1.3** (`thm:unique`). -/
theorem unique_theoremD : Stmt_uniqueD := by
  refine ⟨fun d hd ε hε => ⟨fun v hv hrec => asymptoticsD hd hε hv hrec,
    fun v w hv hw hrv hrw => uniquenessD hd hε hv hw hrv hrw⟩, ?_, ?_⟩
  · intro d hd a ha
    obtain ⟨-, ⟨V0, hV0, -⟩, hsol⟩ := (main_theoremD d (by omega) a ha).2 hd
    -- the norm ratios are the solution of Theorem 1.1(ii)
    have hV0eq : V0 = fun n => signedNormD d a (n + 1) / signedNormD d a n :=
      funext fun n => (hsol V0 hV0 n).2
    have hpos : ∀ n, 0 < signedNormD d a (n + 1) / signedNormD d a n := fun n => by
      have := (hsol V0 hV0 n).1; rwa [hV0eq] at this
    have hrec : FHRec d a (fun n => signedNormD d a (n + 1) / signedNormD d a n) := by
      rw [← hV0eq]; exact hV0.2
    refine ⟨hpos, hrec, fun W hW hWrec => ?_⟩
    have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
    set c : ℝ := a ^ ((2 : ℝ) / ((d : ℝ) - 2)) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos ha _
    have huniq := uniquenessD hd (Real.rpow_pos_of_pos ha _)
      (v := fun n => W n / c) (w := fun n => signedNormD d a (n + 1) / signedNormD d a n / c)
      (fun n => div_pos (hW n) hc0) (fun n => div_pos (hpos n) hc0)
      (fhrec_to_genRec hd ha hWrec) (fhrec_to_genRec hd ha hrec)
    funext n
    exact (div_left_inj' hc0.ne').mp (congrFun huniq n)
  · intro a ha
    obtain ⟨-, -, -, ⟨v, hv, -⟩, hsol⟩ := main_theorem a ha
    have hvpos : ∀ n, 0 < v n := fun n => (hsol v hv n).1
    exact ⟨v, hv, hvpos, fun w hw hwrec => unique_theorem a ha w v hw hvpos hwrec hv.2.2⟩

end Painleve
