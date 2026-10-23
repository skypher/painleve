import Painleve.RecurrenceD
import Painleve.HermIbpD

/-!
# Theorem 1.1 for every `d ≥ 2` (`thm:main`)

Part (i) is `main_partI`. Part (ii): the pairing satisfies the hypotheses of
Section 6, so `V_n = 𝔥_{n+1}/𝔥_n` solves `eq:FH-recurrence`
(`rec_real` and a telescoping product); `P_j = z^j` for `j ≤ d - 1`, so
`𝔥_j = ∫|z|^{2j} ρ_a` and `V_j` has the initial values `eq:FH-initial`; and a
real solution with these initial values is determined index by index, since
the recurrence at `m` is linear in `V_{m+d-2}` with coefficient
`a^{-2} V_m ⋯ V_{m+d-3} > 0`.
-/

open Complex Polynomial Finset
open scoped ComplexConjugate

namespace Painleve

variable {d : ℕ}

theorem formHypD_pairing (hd : 0 < d) {a : ℝ} (ha : 0 < a) : FormHypD d (pairingD d a) a :=
  { add_left := fun f g k => pairingD_add_left a ha f g k
    smul_left := fun c f k => pairingD_C_mul_left a c f k
    herm := fun f g => pairingD_herm hd a ha f g
    weight := fun p q h => pairingD_X_pow_eq_zero hd a p q h
    ibp := fun f q => pairingD_ibp hd a ha f q }

/-- The orthogonal polynomial of degree `n`. -/
noncomputable def opPD (d : ℕ) (a : ℝ) (hdet : ∀ n, (gramLeadD d a n).det ≠ 0) (n : ℕ) : ℂ[X] :=
  Classical.choose (existsUnique_orthoPoly (fun p q => pairingD d a (X ^ p) (X ^ q)) n
    (by rw [← gramLeadD_eq_gramM]; exact hdet n)).exists

theorem opPD_spec (a : ℝ) (hdet : ∀ n, (gramLeadD d a n).det ≠ 0) (n : ℕ) :
    (opPD d a hdet n).Monic ∧ (opPD d a hdet n).natDegree = n ∧
      ∀ j < n, sform (fun p q => pairingD d a (X ^ p) (X ^ q)) (opPD d a hdet n) (X ^ j) = 0 :=
  Classical.choose_spec
    (existsUnique_orthoPoly (fun p q => pairingD d a (X ^ p) (X ^ q)) n
      (by rw [← gramLeadD_eq_gramM]; exact hdet n)).exists

/-- The orthogonal-polynomial data of the pairing. -/
noncomputable def opdataD (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) : OPDataD d (pairingD d a) where
  P := opPD d a (gram_factsD hd ha).1
  h := fun n => signedNormD d a n
  monic := fun n => (opPD_spec a _ n).1
  deg := fun n => (opPD_spec a _ n).2.1
  orth := fun n j hj => by
    rw [pairingD_eq_sform a ha]
    exact (opPD_spec a _ n).2.2 j hj
  norm := fun n => (main_partI hd ha).2 n |>.2.2 _ (opPD_spec a _ n).1 (opPD_spec a _ n).2.1
    (fun j hj => by rw [pairingD_eq_sform a ha]; exact (opPD_spec a _ n).2.2 j hj)
  pos := fun n => (gram_factsD hd ha).2.1 n

/-! ### The recurrence for the norm ratios -/

lemma extZ_nat (v : ℕ → ℝ) (k : ℕ) : extZ v (k : ℤ) = v k := by
  unfold extZ; rw [if_neg (by omega)]; simp

lemma extZ_neg (v : ℕ → ℝ) {k : ℤ} (hk : k < 0) : extZ v k = 0 := by
  unfold extZ; rw [if_pos hk]

/-- Telescoping: `∏_{k<L} V_{t-k} = 𝔥_{t+1}/𝔥_{t+1-L}` for `L ≤ t+1`, else `0`. -/
lemma telescope (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n) (L t : ℕ) :
    ∏ k ∈ range L, extZ (fun n => h (n + 1) / h n) ((t : ℤ) - k)
      = if L ≤ t + 1 then h (t + 1) / h (t + 1 - L) else 0 := by
  induction L with
  | zero => rw [prod_range_zero, if_pos (Nat.zero_le _), Nat.sub_zero, div_self (hpos _).ne']
  | succ L ih =>
    rw [prod_range_succ, ih]
    by_cases hL : L + 1 ≤ t + 1
    · rw [if_pos (by omega), if_pos hL,
        show ((t : ℤ) - (L : ℕ)) = ((t - L : ℕ) : ℤ) by omega, extZ_nat]
      rw [show t - L + 1 = t + 1 - L by omega, show t + 1 - (L + 1) = t - L by omega]
      have := (hpos (t + 1 - L)).ne'
      have := (hpos (t - L)).ne'
      field_simp
    · rw [if_neg hL]
      by_cases hL' : L ≤ t + 1
      · rw [if_pos hL', extZ_neg _ (by omega), mul_zero]
      · rw [if_neg hL', zero_mul]

theorem fhrec_ratio (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    FHRec d a (fun n => signedNormD d a (n + 1) / signedNormD d a n) := by
  intro m
  set D := opdataD hd ha
  have hr := OPDataD.rec_real (formHypD_pairing (by omega) ha) D hd ha m
  have hpos : ∀ n, 0 < D.h n := D.pos
  have hh : ∀ n, D.h n = signedNormD d a n := fun n => rfl
  have hsum : ∑ j ∈ range (d - 1), ∏ k ∈ range (d - 1),
      extZ (fun n => signedNormD d a (n + 1) / signedNormD d a n) ((m : ℤ) + j - k)
      = ∑ s ∈ range (d - 1),
        (if d - 1 ≤ m + 1 + s then D.h (m + 1 + s) / D.h (m + 1 + s + 1 - d) else 0) := by
    refine sum_congr rfl fun s _ => ?_
    have := telescope D.h hpos (d - 1) (m + s)
    simp only [hh] at this
    rw [Finset.prod_congr rfl (fun k _ => by
      rw [show ((m : ℤ) + s - k) = (((m + s : ℕ) : ℤ) - k) by push_cast; ring]), this]
    simp only [hh]
    by_cases hc : d - 1 ≤ m + s + 1
    · rw [if_pos hc, if_pos (by omega), show m + s + 1 = m + 1 + s by ring,
        show m + 1 + s - (d - 1) = m + 1 + s + 1 - d by omega]
    · rw [if_neg hc, if_neg (by omega)]
  rw [hsum]
  simp only [hh] at hr ⊢
  set A := ∑ s ∈ range (d - 1), (if d - 1 ≤ m + 1 + s then
    signedNormD d a (m + 1 + s) / signedNormD d a (m + 1 + s + 1 - d) else 0) with hA
  have h0 : signedNormD d a m ≠ 0 := (hpos m).ne'
  have h1 : signedNormD d a (m + 1) = (((m : ℝ) + 1) * signedNormD d a m
      - (1 / a) * A * signedNormD d a m) / a := by
    rw [eq_div_iff ha.ne']; linarith [hr]
  rw [h1]
  field_simp
  ring

/-! ### Initial values -/

lemma pairingD_X_pow_self (hd : 0 < d) (a : ℝ) (j : ℕ) (hj : j < d) :
    pairingD d a (X ^ j) (X ^ j) = (-1 : ℂ) ^ j * momentD d a j := by
  rw [pairingD_X_pow hd, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, add_zero]
  congr 1
  unfold momentD
  congr 1; funext z
  rw [cast_norm_pow_two_mul z j]

/-- `𝔥_j = ∫|z|^{2j} ρ_a` for `j ≤ d - 1`. -/
theorem signedNormD_eq_moment (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (j : ℕ) (hj : j < d) :
    ((signedNormD d a j : ℝ) : ℂ) = momentD d a j := by
  have hd0 : 0 < d := by omega
  have horth : ∀ i < j, pairingD d a (X ^ j) (X ^ i) = 0 := fun i hi =>
    pairingD_X_pow_eq_zero hd0 a j i (by rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega)]; omega)
  have hn := (main_partI hd ha).2 j |>.2.2 (X ^ j) (monic_X_pow j) (natDegree_X_pow j) horth
  rw [pairingD_X_pow_self hd0 a j hj, rhoSignD_eq hd0, Nat.mod_eq_of_lt hj,
    Nat.div_eq_of_lt hj, add_zero] at hn
  have hsq : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by rw [← mul_pow]; norm_num
  push_cast at hn
  linear_combination (-(-1 : ℂ) ^ j) * hn + (momentD d a j - (signedNormD d a j : ℂ)) * hsq

/-! ### Uniqueness given the initial values -/

theorem fhrec_unique (hd : 3 ≤ d) {a : ℝ} (ha : 0 < a) (V W : ℕ → ℝ) (hV : FHRec d a V)
    (hW : FHRec d a W) (hVpos : ∀ n, 0 < V n) (hinit : ∀ j < d - 2, W j = V j) : W = V := by
  have hext : ∀ n : ℕ, (∀ t : ℤ, t < (n : ℤ) → extZ W t = extZ V t) → W n = V n := by
    intro n hlt
    by_cases hn : n < d - 2
    · exact hinit n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + (d - 2) := ⟨n - (d - 2), by omega⟩
      have e1 := hV m
      have e2 := hW m
      -- split off the top window `j = d - 2` and its top factor `k = 0`
      have hsplit : ∀ U : ℕ → ℝ, ∑ j ∈ range (d - 1), ∏ k ∈ range (d - 1), extZ U ((m : ℤ) + j - k)
          = ∑ j ∈ range (d - 2), ∏ k ∈ range (d - 1), extZ U ((m : ℤ) + j - k)
            + (∏ k ∈ range (d - 2), extZ U ((m : ℤ) + (d - 2 : ℕ) - (k + 1 : ℕ)))
              * U (m + (d - 2)) := by
        intro U
        rw [show d - 1 = (d - 2) + 1 by omega, sum_range_succ, prod_range_succ']
        congr 1
      rw [hsplit] at e1 e2
      have hlow : ∀ t : ℤ, t < (m + (d - 2) : ℕ) → extZ W t = extZ V t := hlt
      have hA : ∑ j ∈ range (d - 2), ∏ k ∈ range (d - 1), extZ W ((m : ℤ) + j - k)
          = ∑ j ∈ range (d - 2), ∏ k ∈ range (d - 1), extZ V ((m : ℤ) + j - k) :=
        sum_congr rfl fun j hj => prod_congr rfl fun k _ => hlow _ (by
          have := mem_range.mp hj; push_cast; omega)
      have hQ : ∏ k ∈ range (d - 2), extZ W ((m : ℤ) + (d - 2 : ℕ) - (k + 1 : ℕ))
          = ∏ k ∈ range (d - 2), extZ V ((m : ℤ) + (d - 2 : ℕ) - (k + 1 : ℕ)) :=
        prod_congr rfl fun k hk => hlow _ (by have := mem_range.mp hk; push_cast; omega)
      have hm : W m = V m := by
        have := hlow (m : ℤ) (by push_cast; omega)
        rwa [extZ_nat, extZ_nat] at this
      have hQpos : 0 < ∏ k ∈ range (d - 2), extZ V ((m : ℤ) + (d - 2 : ℕ) - (k + 1 : ℕ)) := by
        refine prod_pos fun k hk => ?_
        have hk' := mem_range.mp hk
        rw [show ((m : ℤ) + ((d - 2 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)) = ((m + (d - 2) - (k + 1) : ℕ) : ℤ)
          by push_cast [Nat.cast_sub (show k + 1 ≤ m + (d - 2) by omega)]; ring, extZ_nat]
        exact hVpos _
      rw [hA, hQ, hm] at e2
      have ha2 : (0 : ℝ) < 1 / a ^ 2 := by positivity
      have key : (1 / a ^ 2 * ∏ k ∈ range (d - 2), extZ V ((m : ℤ) + (d - 2 : ℕ) - (k + 1 : ℕ)))
          * (W (m + (d - 2)) - V (m + (d - 2))) = 0 := by
        linear_combination e2 - e1
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h (mul_pos ha2 hQpos).ne'
      · exact sub_eq_zero.mp h
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    refine hext n fun t ht => ?_
    by_cases ht0 : t < 0
    · rw [extZ_neg _ ht0, extZ_neg _ ht0]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = k := ⟨t.toNat, by omega⟩
      rw [extZ_nat, extZ_nat]
      exact ih k (by omega)

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1** (`thm:main`) for every `d ≥ 2`. -/
theorem main_theoremD : Stmt_mainD := by
  intro d hd a ha
  refine ⟨main_partI hd ha, fun hd3 => ?_⟩
  have hpos : ∀ n, 0 < signedNormD d a n := (gram_factsD hd ha).2.1
  set V : ℕ → ℝ := fun n => signedNormD d a (n + 1) / signedNormD d a n with hVdef
  have hVpos : ∀ n, 0 < V n := fun n => div_pos (hpos (n + 1)) (hpos n)
  have hVrec : FHRec d a V := fhrec_ratio hd ha
  have hmom : ∀ j < d - 1, momentD d a j = ((signedNormD d a j : ℝ) : ℂ) :=
    fun j hj => (signedNormD_eq_moment hd ha j (by omega)).symm
  have hVsol : IsSolD d a V := by
    refine ⟨fun j hj => ?_, hVrec⟩
    rw [hmom j (by omega), hmom (j + 1) (by omega), hVdef]
    push_cast
    rfl
  refine ⟨fun j hj => ?_, ⟨V, hVsol, fun W hW => ?_⟩, fun W hW n => ?_⟩
  · rw [hmom j (by omega)]
    exact Complex.ofReal_ne_zero.mpr (hpos j).ne'
  · refine fhrec_unique hd3 ha V W hVrec hW.2 hVpos fun j hj => ?_
    have h1 := hW.1 j hj
    have h2 := hVsol.1 j hj
    exact_mod_cast h1.trans h2.symm
  · have hWV : W = V := fhrec_unique hd3 ha V W hVrec hW.2 hVpos fun j hj => by
      have h1 := hW.1 j hj
      have h2 := hVsol.1 j hj
      exact_mod_cast h1.trans h2.symm
    rw [hWV]
    exact ⟨hVpos n, rfl⟩

end Painleve
