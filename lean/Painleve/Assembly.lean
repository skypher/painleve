import Painleve.Recurrence
import Painleve.Herm
import Painleve.Ibp
import Painleve.Gram
import Painleve.OrthoPoly
import Painleve.Signs

open Complex Polynomial
open scoped ComplexConjugate

namespace Painleve

theorem formHyp_pairing (a : ℝ) (ha : 0 < a) : FormHyp (pairing a) a :=
  { add_left := fun f g k => pairing_add_left a ha f g k
    smul_left := fun c f k => pairing_C_mul_left a c f k
    herm := fun f g => pairing_herm a ha f g
    weight := fun p q h => pairing_X_pow_eq_zero a p q h
    ibp := fun f q => pairing_ibp_of_moment a ha (fun p q => moment_ibp a ha p q) f q }

lemma tri_lemma (J : ℕ) : (J + 1) * (J + 1 - 1) / 2 = J * (J - 1) / 2 + J := by
  cases J with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    have h : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

lemma sign_ratio (n : ℕ) :
    (-1 : ℝ) ^ (n % 4 * (n / 4 + 1) + (n / 4 + 1) * (n / 4 + 1 - 1) / 2)
      = (-1 : ℝ) ^ (n % 4 * (n / 4) + (n / 4) * (n / 4 - 1) / 2) * rhoSign n := by
  rw [rhoSign_eq, ← pow_add, neg_one_pow_eq_pow_mod_two
    (n := n % 4 * (n / 4 + 1) + (n / 4 + 1) * (n / 4 + 1 - 1) / 2),
    neg_one_pow_eq_pow_mod_two
    (n := n % 4 * (n / 4) + (n / 4) * (n / 4 - 1) / 2 + (n + n / 4))]
  congr 1
  rw [tri_lemma]
  have hm : n % 4 * (n / 4 + 1) = n % 4 * (n / 4) + n % 4 := by ring
  rw [hm]
  generalize n % 4 * (n / 4) = M
  generalize n / 4 * (n / 4 - 1) / 2 = T
  omega

lemma blk_ne (a : ℝ) (hsign : ∀ r k : ℕ, r < 4 → ∃ c : ℝ, 0 < c ∧
      (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ))
    (r k : ℕ) (hr : r < 4) : (blockGram a r k).det ≠ 0 := by
  obtain ⟨c, hc, hd⟩ := hsign r k hr
  rw [hd]
  exact Complex.ofReal_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc.ne')

lemma gram_ne (a : ℝ) (hsign : ∀ r k : ℕ, r < 4 → ∃ c : ℝ, 0 < c ∧
      (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ))
    (n : ℕ) : (gramLead a n).det ≠ 0 := by
  rw [det_gramLead_eq_prod, Finset.prod_ne_zero_iff]
  intro r _
  exact blk_ne a hsign r ((n + 3 - r) / 4) r.isLt

lemma ratio_claim (a : ℝ) (hsign : ∀ r k : ℕ, r < 4 → ∃ c : ℝ, 0 < c ∧
      (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ))
    (n : ℕ) : ∃ c : ℝ, 0 < c ∧
      (gramLead a (n + 1)).det / (gramLead a n).det = ((rhoSign n * c : ℝ) : ℂ) := by
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  obtain ⟨c, hc, hd⟩ := hsign (n % 4) (n / 4) hr
  obtain ⟨c', hc', hd'⟩ := hsign (n % 4) (n / 4 + 1) hr
  refine ⟨c' / c, div_pos hc' hc, ?_⟩
  rw [det_gramLead_eq_prod a (n + 1), det_gramLead_eq_prod a n]
  have hmem : (⟨n % 4, hr⟩ : Fin 4) ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ _
  rw [← Finset.mul_prod_erase Finset.univ _ hmem, ← Finset.mul_prod_erase Finset.univ _ hmem]
  have hQ : ∏ x ∈ (Finset.univ : Finset (Fin 4)).erase ⟨n % 4, hr⟩,
      (blockGram a (x : ℕ) ((n + 1 + 3 - (x : ℕ)) / 4)).det
      = ∏ x ∈ (Finset.univ : Finset (Fin 4)).erase ⟨n % 4, hr⟩,
      (blockGram a (x : ℕ) ((n + 3 - (x : ℕ)) / 4)).det := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ (⟨n % 4, hr⟩ : Fin 4) := Finset.ne_of_mem_erase hx
    have hxv : (x : ℕ) ≠ n % 4 := fun h => hne (Fin.ext h)
    have hx4 : (x : ℕ) < 4 := x.isLt
    have e : (n + 1 + 3 - (x : ℕ)) / 4 = (n + 3 - (x : ℕ)) / 4 := by omega
    rw [e]
  have hQne : ∏ x ∈ (Finset.univ : Finset (Fin 4)).erase ⟨n % 4, hr⟩,
      (blockGram a (x : ℕ) ((n + 3 - (x : ℕ)) / 4)).det ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun x _ => blk_ne a hsign x _ x.isLt)
  simp only [Fin.val_mk]
  have e1 : (n + 1 + 3 - n % 4) / 4 = n / 4 + 1 := by omega
  have e0 : (n + 3 - n % 4) / 4 = n / 4 := by omega
  rw [e1, e0, hQ, hd', hd, mul_div_mul_right _ _ hQne, ← Complex.ofReal_div]
  congr 1
  rw [sign_ratio n]
  have hσ : (-1 : ℝ) ^ (n % 4 * (n / 4) + (n / 4) * (n / 4 - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  field_simp

lemma rhoSign_sq (n : ℕ) : rhoSign n * rhoSign n = 1 := by
  rw [rhoSign_eq, ← mul_pow]
  norm_num

lemma signedNorm_of_ratio (a : ℝ) (n : ℕ) (c : ℝ)
    (hr : (gramLead a (n + 1)).det / (gramLead a n).det = ((rhoSign n * c : ℝ) : ℂ)) :
    signedNorm a n = c := by
  unfold signedNorm
  rw [hr, Complex.ofReal_re, ← mul_assoc, rhoSign_sq, one_mul]

theorem gram_facts (a : ℝ) (ha : 0 < a)
    (hsign : ∀ r k : ℕ, r < 4 → ∃ c : ℝ, 0 < c ∧
      (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ)) :
    (∀ n, (gramLead a n).det ≠ 0) ∧
    (∀ n, 0 < signedNorm a n) ∧
    (∀ n, ((gramLead a (n + 1)).det / (gramLead a n).det) = ((rhoSign n * signedNorm a n : ℝ) : ℂ)) := by
  refine ⟨gram_ne a hsign, fun n => ?_, fun n => ?_⟩
  · obtain ⟨c, hc, hr⟩ := ratio_claim a hsign n
    rw [signedNorm_of_ratio a n c hr]
    exact hc
  · obtain ⟨c, hc, hr⟩ := ratio_claim a hsign n
    rw [signedNorm_of_ratio a n c hr]
    exact hr

/-- The orthogonal polynomial of degree `n`, chosen from the existence part. -/
noncomputable def opP (a : ℝ) (hdet : ∀ n, (gramLead a n).det ≠ 0) (n : ℕ) : ℂ[X] :=
  Classical.choose (existsUnique_orthoPoly (fun p q => pairing a (X ^ p) (X ^ q)) n (hdet n)).exists

theorem opP_spec (a : ℝ) (hdet : ∀ n, (gramLead a n).det ≠ 0) (n : ℕ) :
    (opP a hdet n).Monic ∧ (opP a hdet n).natDegree = n ∧
      ∀ j < n, sform (fun p q => pairing a (X ^ p) (X ^ q)) (opP a hdet n) (X ^ j) = 0 :=
  Classical.choose_spec
    (existsUnique_orthoPoly (fun p q => pairing a (X ^ p) (X ^ q)) n (hdet n)).exists

/-- The orthogonal polynomial data of the pairing. -/
noncomputable def opdata (a : ℝ) (ha : 0 < a) (hdet : ∀ n, (gramLead a n).det ≠ 0)
    (hpos : ∀ n, 0 < signedNorm a n)
    (hratio : ∀ n, ((gramLead a (n + 1)).det / (gramLead a n).det) =
      ((rhoSign n * signedNorm a n : ℝ) : ℂ)) : OPData (pairing a) where
  P := opP a hdet
  h := fun n => signedNorm a n
  monic := fun n => (opP_spec a hdet n).1
  deg := fun n => (opP_spec a hdet n).2.1
  orth := fun n j hj => by
    rw [pairing_eq_sform a ha]
    exact (opP_spec a hdet n).2.2 j hj
  norm := fun n => by
    have hD := sform_self_mul_det (fun p q => pairing a (X ^ p) (X ^ q)) n (opP a hdet n)
      (opP_spec a hdet n).1 (opP_spec a hdet n).2.1 (opP_spec a hdet n).2.2
    rw [← pairing_eq_sform a ha] at hD
    have hD' : pairing a (opP a hdet n) (opP a hdet n) * (gramLead a n).det
        = (gramLead a (n + 1)).det := hD
    have hq : pairing a (opP a hdet n) (opP a hdet n)
        = (gramLead a (n + 1)).det / (gramLead a n).det :=
      (eq_div_iff (hdet n)).2 hD'
    rw [hq, hratio n]
  pos := hpos

theorem opdata_h (a : ℝ) (ha : 0 < a) (hdet : ∀ n, (gramLead a n).det ≠ 0)
    (hpos : ∀ n, 0 < signedNorm a n)
    (hratio : ∀ n, ((gramLead a (n + 1)).det / (gramLead a n).det) =
      ((rhoSign n * signedNorm a n : ℝ) : ℂ)) (n : ℕ) :
    (opdata a ha hdet hpos hratio).h n = signedNorm a n := rfl

theorem opdata_P_spec (a : ℝ) (ha : 0 < a) (hdet : ∀ n, (gramLead a n).det ≠ 0)
    (hpos : ∀ n, 0 < signedNorm a n)
    (hratio : ∀ n, ((gramLead a (n + 1)).det / (gramLead a n).det) =
      ((rhoSign n * signedNorm a n : ℝ) : ℂ)) (n : ℕ) :
    ((opdata a ha hdet hpos hratio).P n).Monic ∧ ((opdata a ha hdet hpos hratio).P n).natDegree = n ∧
      ∀ j < n, pairing a ((opdata a ha hdet hpos hratio).P n) (X ^ j) = 0 := by
  refine ⟨(opP_spec a hdet n).1, (opP_spec a hdet n).2.1, fun j hj => ?_⟩
  rw [pairing_eq_sform a ha]
  exact (opP_spec a hdet n).2.2 j hj

end Painleve
