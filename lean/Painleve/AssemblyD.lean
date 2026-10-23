import Painleve.BlockSignD
import Painleve.OrthoPoly
import Painleve.Assembly

/-!
# Theorem 1.1(i) for general `d`: nondegeneracy and positive signed norms

From the block signs (`blockGramD_sign`, Proposition 5.2):
`det G_{n+1}/det G_n = ϱ(n) c` with `c > 0` (`eq:norm-delta-ratio`,
`eq:rho-block`), so every leading Gram matrix is nondegenerate and `𝔥_n > 0`.
-/

open Complex Polynomial
open scoped ComplexConjugate

namespace Painleve

variable {d : ℕ}

/-- `ϱ(n) = (-1)^{n mod d + ⌊n/d⌋}` (`eq:rho-block`). -/
theorem rhoSignD_eq (hd : 0 < d) (n : ℕ) : rhoSignD d n = (-1) ^ (n % d + n / d) := by
  induction n with
  | zero => simp [rhoSignD]
  | succ n ih =>
    have hstep : rhoSignD d (n + 1) = -tauD d n * rhoSignD d n := by
      unfold rhoSignD; rw [Finset.prod_range_succ]; ring
    rw [hstep, ih]
    have hq := Nat.div_add_mod n d
    have hm := Nat.mod_lt n hd
    by_cases hlast : n % d = d - 1
    · have ht : tauD d n = (-1) ^ (d - 1) := by unfold tauD; rw [if_pos hlast]
      have e1 : (n + 1) % d = 0 := by
        have : n + 1 = d * (n / d + 1) := by
          rw [Nat.mul_succ]; omega
        rw [this, Nat.mul_mod_right]
      have e2 : (n + 1) / d = n / d + 1 := by
        have : n + 1 = d * (n / d + 1) := by
          rw [Nat.mul_succ]; omega
        rw [this, Nat.mul_div_cancel_left _ hd]
      rw [ht, e1, e2, hlast]
      have h2 : ((-1 : ℝ) ^ (d - 1)) * (-1) ^ (d - 1) = 1 := by rw [← mul_pow]; norm_num
      have : (-1 : ℝ) ^ (d - 1 + n / d) = (-1) ^ (d - 1) * (-1) ^ (n / d) := pow_add _ _ _
      rw [this, zero_add, pow_succ]
      linear_combination (-(-1 : ℝ) ^ (n / d)) * h2
    · have ht : tauD d n = 1 := by unfold tauD; rw [if_neg hlast]
      have hlt : n % d + 1 < d := by omega
      have e1 : (n + 1) % d = n % d + 1 := by
        have : n + 1 = (n % d + 1) + d * (n / d) := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      have e2 : (n + 1) / d = n / d := by
        have : n + 1 = (n % d + 1) + d * (n / d) := by omega
        rw [this, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hlt, zero_add]
      rw [ht, e1, e2, show n % d + 1 + n / d = (n % d + n / d) + 1 by ring, pow_succ]
      ring

lemma rhoSignD_sq (hd : 0 < d) (n : ℕ) : rhoSignD d n * rhoSignD d n = 1 := by
  rw [rhoSignD_eq hd, ← mul_pow]; norm_num

/-- Block sizes: `⌊(n + d - 1 - r)/d⌋ = ⌊n/d⌋ + [r < n mod d]` for `r < d`. -/
lemma blk_size (hd : 0 < d) (n r : ℕ) (hr : r < d) :
    (n + d - 1 - r) / d = n / d + (if r < n % d then 1 else 0) := by
  have hq := Nat.div_add_mod n d
  have hm := Nat.mod_lt n hd
  have hsplit : n + d - 1 - r = (n % d + d - 1 - r) + d * (n / d) := by omega
  rw [hsplit, Nat.add_mul_div_left _ _ hd, add_comm]
  congr 1
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

lemma blk_size_succ (hd : 0 < d) (n r : ℕ) (hr : r < d) :
    (n + 1 + d - 1 - r) / d = (n + d - 1 - r) / d + (if r = n % d then 1 else 0) := by
  rw [blk_size hd n r hr, blk_size hd (n + 1) r hr]
  have hq := Nat.div_add_mod n d
  have hm := Nat.mod_lt n hd
  by_cases hlast : n % d = d - 1
  · have e1 : (n + 1) % d = 0 := by
      have : n + 1 = d * (n / d + 1) := by rw [Nat.mul_succ]; omega
      rw [this, Nat.mul_mod_right]
    have e2 : (n + 1) / d = n / d + 1 := by
      have : n + 1 = d * (n / d + 1) := by rw [Nat.mul_succ]; omega
      rw [this, Nat.mul_div_cancel_left _ hd]
    rw [e1, e2]
    split_ifs <;> omega
  · have hlt : n % d + 1 < d := by omega
    have e1 : (n + 1) % d = n % d + 1 := by
      have : n + 1 = (n % d + 1) + d * (n / d) := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have e2 : (n + 1) / d = n / d := by
      have : n + 1 = (n % d + 1) + d * (n / d) := by omega
      rw [this, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hlt, zero_add]
    rw [e1, e2]
    split_ifs <;> omega

lemma blk_size_self (hd : 0 < d) (n : ℕ) : (n + d - 1 - n % d) / d = n / d := by
  rw [blk_size hd n (n % d) (Nat.mod_lt n hd), if_neg (lt_irrefl _), add_zero]

lemma sign_ratioD (hd : 0 < d) (n : ℕ) :
    (-1 : ℝ) ^ (n % d * (n / d + 1) + (n / d + 1) * (n / d + 1 - 1) / 2)
      = (-1 : ℝ) ^ (n % d * (n / d) + (n / d) * (n / d - 1) / 2) * rhoSignD d n := by
  rw [rhoSignD_eq hd, ← pow_add, neg_one_pow_eq_pow_mod_two
    (n := n % d * (n / d + 1) + (n / d + 1) * (n / d + 1 - 1) / 2),
    neg_one_pow_eq_pow_mod_two
    (n := n % d * (n / d) + (n / d) * (n / d - 1) / 2 + (n % d + n / d))]
  congr 1
  rw [tri_lemma]
  have hm : n % d * (n / d + 1) = n % d * (n / d) + n % d := by ring
  rw [hm]
  generalize n % d * (n / d) = M
  generalize n / d * (n / d - 1) / 2 = T
  omega

lemma blkD_ne (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (r k : ℕ) (hr : r < d) :
    (blockGramD d a r k).det ≠ 0 := by
  obtain ⟨c, hc, hdet⟩ := blockGramD_sign hd ha r k hr
  rw [hdet]
  exact Complex.ofReal_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc.ne')

theorem gramD_ne (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (n : ℕ) : (gramLeadD d a n).det ≠ 0 := by
  have hd0 : 0 < d := by omega
  rw [det_gramLeadD_eq_prod hd0, Finset.prod_ne_zero_iff]
  intro r _
  exact blkD_ne hd ha r _ r.isLt

theorem ratio_claimD (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (n : ℕ) : ∃ c : ℝ, 0 < c ∧
    (gramLeadD d a (n + 1)).det / (gramLeadD d a n).det = ((rhoSignD d n * c : ℝ) : ℂ) := by
  have hd0 : 0 < d := by omega
  have hr : n % d < d := Nat.mod_lt _ hd0
  obtain ⟨c, hc, hdc⟩ := blockGramD_sign hd ha (n % d) (n / d) hr
  obtain ⟨c', hc', hdc'⟩ := blockGramD_sign hd ha (n % d) (n / d + 1) hr
  refine ⟨c' / c, div_pos hc' hc, ?_⟩
  rw [det_gramLeadD_eq_prod hd0 a (n + 1), det_gramLeadD_eq_prod hd0 a n]
  have hmem : (⟨n % d, hr⟩ : Fin d) ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
  rw [← Finset.mul_prod_erase Finset.univ _ hmem, ← Finset.mul_prod_erase Finset.univ _ hmem]
  have hQ : ∏ x ∈ (Finset.univ : Finset (Fin d)).erase ⟨n % d, hr⟩,
      (blockGramD d a (x : ℕ) ((n + 1 + d - 1 - (x : ℕ)) / d)).det
      = ∏ x ∈ (Finset.univ : Finset (Fin d)).erase ⟨n % d, hr⟩,
      (blockGramD d a (x : ℕ) ((n + d - 1 - (x : ℕ)) / d)).det := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ (⟨n % d, hr⟩ : Fin d) := Finset.ne_of_mem_erase hx
    have hxv : (x : ℕ) ≠ n % d := fun h => hne (Fin.ext h)
    rw [blk_size_succ hd0 n x x.isLt, if_neg hxv, add_zero]
  have hQne : ∏ x ∈ (Finset.univ : Finset (Fin d)).erase ⟨n % d, hr⟩,
      (blockGramD d a (x : ℕ) ((n + d - 1 - (x : ℕ)) / d)).det ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun x _ => blkD_ne hd ha x _ x.isLt)
  simp only [Fin.val_mk]
  rw [blk_size_succ hd0 n (n % d) hr, if_pos rfl, blk_size_self hd0 n, hQ, hdc', hdc,
    mul_div_mul_right _ _ hQne, ← Complex.ofReal_div]
  congr 1
  rw [sign_ratioD hd0 n]
  have hσ : (-1 : ℝ) ^ (n % d * (n / d) + (n / d) * (n / d - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  field_simp

lemma signedNormD_of_ratio (hd : 0 < d) (a : ℝ) (n : ℕ) (c : ℝ)
    (hr : (gramLeadD d a (n + 1)).det / (gramLeadD d a n).det = ((rhoSignD d n * c : ℝ) : ℂ)) :
    signedNormD d a n = c := by
  unfold signedNormD
  rw [hr, Complex.ofReal_re, ← mul_assoc, rhoSignD_sq hd, one_mul]

/-- Nondegeneracy, positivity of the signed norms and the determinant ratio. -/
theorem gram_factsD (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    (∀ n, (gramLeadD d a n).det ≠ 0) ∧
    (∀ n, 0 < signedNormD d a n) ∧
    (∀ n, ((gramLeadD d a (n + 1)).det / (gramLeadD d a n).det) =
      ((rhoSignD d n * signedNormD d a n : ℝ) : ℂ)) := by
  have hd0 : 0 < d := by omega
  refine ⟨gramD_ne hd ha, fun n => ?_, fun n => ?_⟩
  · obtain ⟨c, hc, hr⟩ := ratio_claimD hd ha n
    rw [signedNormD_of_ratio hd0 a n c hr]
    exact hc
  · obtain ⟨c, hc, hr⟩ := ratio_claimD hd ha n
    rw [signedNormD_of_ratio hd0 a n c hr]
    exact hr

/-- **Theorem 1.1(i)** for every `d ≥ 2`. -/
theorem main_partI (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    (∀ n : ℕ, (gramLeadD d a n).det ≠ 0) ∧
      ∀ n : ℕ, 0 < signedNormD d a n ∧
        (∃! P : ℂ[X], P.Monic ∧ P.natDegree = n ∧ ∀ j < n, pairingD d a P (X ^ j) = 0) ∧
        ∀ P : ℂ[X], P.Monic → P.natDegree = n → (∀ j < n, pairingD d a P (X ^ j) = 0) →
          pairingD d a P P = ((rhoSignD d n * signedNormD d a n : ℝ) : ℂ) := by
  obtain ⟨hdet, hpos, hratio⟩ := gram_factsD hd ha
  set G : ℕ → ℕ → ℂ := fun p q => pairingD d a (X ^ p) (X ^ q) with hG
  have hnorm : ∀ n (P : ℂ[X]), P.Monic → P.natDegree = n → (∀ j < n, pairingD d a P (X ^ j) = 0) →
      pairingD d a P P = ((rhoSignD d n * signedNormD d a n : ℝ) : ℂ) := by
    intro n P hm hdg ho
    have ho' : ∀ j < n, sform G P (X ^ j) = 0 := fun j hj => by
      rw [← pairingD_eq_sform a ha]; exact ho j hj
    have h := sform_self_mul_det G n P hm hdg ho'
    rw [← pairingD_eq_sform a ha, ← gramLeadD_eq_gramM, ← gramLeadD_eq_gramM] at h
    rw [← hratio n, eq_div_iff (hdet n)]
    exact h
  refine ⟨hdet, fun n => ⟨hpos n, ?_, hnorm n⟩⟩
  obtain ⟨P, ⟨hPm, hPd, hPo⟩, huniq⟩ :=
    existsUnique_orthoPoly G n (by rw [← gramLeadD_eq_gramM]; exact hdet n)
  refine ⟨P, ⟨hPm, hPd, fun j hj => ?_⟩, fun Q ⟨hQm, hQd, hQo⟩ => huniq Q ⟨hQm, hQd, fun j hj => ?_⟩⟩
  · rw [pairingD_eq_sform a ha]; exact hPo j hj
  · rw [← pairingD_eq_sform a ha]; exact hQo j hj

end Painleve
