import Painleve.Assembly
import Painleve.Uniq
import Painleve.PlanarOde
import Painleve.HSeries
import Painleve.PhiHankel

/-!
# Assembly of Theorem 1.1 from the block signs and the Bessel identification

`main_of` derives `Stmt_main` from two inputs proved in separate modules:
the sign of every Gram block determinant (Proposition 4.4) and the
identification `∫ ρ_a = h(a)` of the planar integral with the Bessel
combination (Lemma 5.1).
-/

open Complex Polynomial Filter
open scoped ComplexConjugate ContDiff Topology

namespace Painleve

/-- The initial monomials are the monic orthogonal polynomials of degree `≤ 3`. -/
theorem X_pow_orth (a : ℝ) (k : ℕ) (hk : k ≤ 3) : ∀ j < k, pairing a (X ^ k) (X ^ j) = 0 := by
  intro j hj
  exact pairing_X_pow_eq_zero a k j (by omega)

theorem pairing_X_pow_self (a : ℝ) (k : ℕ) :
    pairing a (X ^ k) (X ^ k) = (-1 : ℂ) ^ (k % 4 + k / 4) * mom a k k := by
  rw [pairing_X_pow]; rfl

/-- Derivatives of a function that agrees with a smooth real function near `a`. -/
theorem iteratedDeriv_eq_of_eqOn {f : ℝ → ℂ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {a : ℝ}
    (ha : 0 < a) (hfg : ∀ x, 0 < x → f x = (g x : ℂ)) (k : ℕ) :
    iteratedDeriv k f a = ((iteratedDeriv k g a : ℝ) : ℂ) := by
  have hev : f =ᶠ[𝓝 a] fun x => ((g x : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds ha] with x hx using hfg x hx
  have h1 : iteratedDeriv k f a = iteratedDeriv k (fun x => ((g x : ℝ) : ℂ)) a :=
    hev.iteratedDeriv_eq k
  rw [h1, iteratedDeriv_ofReal_comm g isOpen_univ hg.contDiffOn k a (Set.mem_univ a)]

/-- Real derivatives of a real function that agrees with a smooth one on `(0,∞)`. -/
theorem iteratedDeriv_real_eq_of_eqOn {f g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hfg : ∀ x, 0 < x → f x = g x) (k : ℕ) : iteratedDeriv k f a = iteratedDeriv k g a := by
  have hev : f =ᶠ[𝓝 a] g := by
    filter_upwards [Ioi_mem_nhds ha] with x hx using hfg x hx
  exact hev.iteratedDeriv_eq k

theorem main_of
    (hblock : ∀ a : ℝ, 0 < a → ∀ r k : ℕ, r < 4 → ∃ c : ℝ, 0 < c ∧
      (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ))
    (hbes : ∀ a : ℝ, 0 < a → hPlanar a = ((hBessel a : ℝ) : ℂ)) :
    Stmt_main := by
  intro a ha
  obtain ⟨hdet, hpos, hratio⟩ := gram_facts a ha (hblock a ha)
  set G : ℕ → ℕ → ℂ := fun p q => pairing a (X ^ p) (X ^ q) with hG
  -- the norm identity for any monic orthogonal polynomial
  have hnorm : ∀ n (P : ℂ[X]), P.Monic → P.natDegree = n → (∀ j < n, pairing a P (X ^ j) = 0) →
      pairing a P P = ((rhoSign n * signedNorm a n : ℝ) : ℂ) := by
    intro n P hm hd ho
    have ho' : ∀ j < n, sform G P (X ^ j) = 0 := fun j hj => by
      rw [← pairing_eq_sform a ha]; exact ho j hj
    have h := sform_self_mul_det G n P hm hd ho'
    rw [← pairing_eq_sform a ha, ← gramLead_eq_gramM, ← gramLead_eq_gramM] at h
    rw [← hratio n, eq_div_iff (hdet n)]
    exact h
  -- the first three signed norms in terms of the planar integral
  have hsq : ∀ k ≤ 2, pairing a (X ^ k) (X ^ k) = ((rhoSign k * signedNorm a k : ℝ) : ℂ) :=
    fun k hk => hnorm k (X ^ k) (monic_X_pow k) (natDegree_X_pow k) (X_pow_orth a k (by omega))
  have hρ0 : rhoSign 0 = 1 := by rw [rhoSign_eq]; norm_num
  have hρ1 : rhoSign 1 = -1 := by rw [rhoSign_eq]; norm_num
  have hρ2 : rhoSign 2 = 1 := by rw [rhoSign_eq]; norm_num
  have hm0 : mom a 0 0 = hPlanar a := by unfold mom hPlanar; simp
  have hS : ∀ x, 0 < x → hPlanar x = ((hSeries x : ℝ) : ℂ) := fun x hx => by
    rw [hbes x hx, hBessel_eq_hSeries x hx]
  have hdS : ∀ k, iteratedDeriv k hPlanar a = ((iteratedDeriv k hSeries a : ℝ) : ℂ) :=
    iteratedDeriv_eq_of_eqOn hSeries_contDiff ha hS
  have hdB : ∀ k, iteratedDeriv k hBessel a = iteratedDeriv k hSeries a :=
    iteratedDeriv_real_eq_of_eqOn ha (fun x hx => hBessel_eq_hSeries x hx)
  have h0 : hBessel a = signedNorm a 0 := by
    have e := hsq 0 (by norm_num)
    rw [pairing_X_pow_self, hρ0] at e
    simp only [pow_zero, Nat.zero_mod, Nat.zero_div, add_zero, one_mul, hm0, hbes a ha] at e
    exact_mod_cast e
  have h1 : deriv hBessel a = -signedNorm a 1 := by
    have e := hsq 1 (by norm_num)
    rw [pairing_X_pow_self, hρ1] at e
    have hd := iteratedDeriv_hPlanar 1 a ha
    rw [hdS 1, ← hdB 1, iteratedDeriv_one] at hd
    norm_num at e hd
    have : ((deriv hBessel a : ℝ) : ℂ) = ((-signedNorm a 1 : ℝ) : ℂ) := by
      rw [hd]; push_cast; linear_combination -e
    exact_mod_cast this
  have h2 : deriv (deriv hBessel) a = signedNorm a 2 := by
    have e := hsq 2 (by norm_num)
    rw [pairing_X_pow_self, hρ2] at e
    have hd := iteratedDeriv_hPlanar 2 a ha
    rw [hdS 2, ← hdB 2, iteratedDeriv_succ, iteratedDeriv_one] at hd
    norm_num at e hd
    have : ((deriv (deriv hBessel) a : ℝ) : ℂ) = ((signedNorm a 2 : ℝ) : ℂ) := by
      rw [hd, e]
    exact_mod_cast this
  -- the orthogonal-polynomial data and the recurrence
  set D := opdata a ha hdet hpos hratio with hD
  have hrec : QuarticRec a (fun n => signedNorm a (n + 1) / (a * signedNorm a n)) :=
    OPData.quarticRec (formHyp_pairing a ha) D ha
  set v : ℕ → ℝ := fun n => signedNorm a (n + 1) / (a * signedNorm a n) with hv
  have hvpos : ∀ n, 0 < v n := fun n =>
    div_pos (hpos (n + 1)) (mul_pos ha (hpos n))
  have hv0 : v 0 = v0 a := by
    simp only [hv, v0, h0, h1]; ring
  have hv1 : v 1 = v1 a := by
    simp only [hv, v1, h1, h2]
    have := (hpos 1).ne'
    field_simp
  have hsol : IsSolution a v := ⟨hv0, hv1, hrec⟩
  refine ⟨⟨hdet, fun n => ⟨hpos n, ?_, hnorm n⟩⟩, ?_⟩
  · obtain ⟨P, ⟨hPm, hPd, hPo⟩, huniq⟩ :=
      existsUnique_orthoPoly G n (by rw [← gramLead_eq_gramM]; exact hdet n)
    refine ⟨P, ⟨hPm, hPd, fun j hj => ?_⟩, fun Q ⟨hQm, hQd, hQo⟩ => huniq Q ⟨hQm, hQd, fun j hj => ?_⟩⟩
    · rw [pairing_eq_sform a ha]; exact hPo j hj
    · rw [← pairing_eq_sform a ha]; exact hQo j hj
  · refine ⟨?_, ?_, ⟨v, hsol, fun w hw => ?_⟩, fun w hw n => ?_⟩
    · rw [h0]; exact (hpos 0).ne'
    · rw [h1]; exact neg_ne_zero.mpr (hpos 1).ne'
    · exact (quarticRec_unique a v w hrec hw.2.2 (hv0.trans hw.1.symm)
        (hv1.trans hw.2.1.symm) hvpos).symm
    · have hwv : w = v := (quarticRec_unique a v w hrec hw.2.2 (hv0.trans hw.1.symm)
        (hv1.trans hw.2.1.symm) hvpos).symm
      rw [hwv]
      exact ⟨hvpos n, rfl⟩

end Painleve
