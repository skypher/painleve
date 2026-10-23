import Painleve.AssemblyD
import Painleve.Ibp
import Painleve.Herm

/-!
# Hermitian symmetry and integration by parts for general `d` (Section 6)

`(f, g)_a = conj (g, f)_a`, and with `L = ∂_z + i z^{d-1}`,
`(L f, z^q)_a = -τ(q) a (f, z^{q+1})_a` (`eq:ibp-pairing`), from
`∂_z ρ_a = (-a z̄ + i z^{d-1}) ρ_a` and the vanishing of total derivatives.
-/

open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

variable {d : ℕ}

/-! ### Hermitian symmetry -/

lemma etaD_mul_conj : etaD d * conj (etaD d) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_etaD]; norm_num

theorem conj_momentD (hd : 0 < d) (a : ℝ) (p q : ℕ) :
    conj (∫ z : ℂ, z ^ q * conj z ^ p * densityD d a z) =
      conj (etaD d) ^ p * etaD d ^ q * ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z := by
  rw [← integral_conj]
  have hL : ∫ z : ℂ, conj (z ^ q * conj z ^ p * densityD d a z)
      = ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a (etaD d * z) := by
    congr 1; funext z
    simp only [map_mul, map_pow, conj_conj, ← densityD_eta_mul hd]
    ring
  have hu : ‖conj (etaD d)‖ = 1 := by rw [Complex.norm_conj, norm_etaD]
  have hrot : ∫ z : ℂ, (conj (etaD d) * z) ^ p * conj (conj (etaD d) * z) ^ q *
      densityD d a (etaD d * (conj (etaD d) * z))
      = ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a (etaD d * z) :=
    integral_rot_unit (conj (etaD d)) hu (fun z => z ^ p * conj z ^ q * densityD d a (etaD d * z))
  rw [hL, ← hrot, ← integral_const_mul]
  congr 1; funext z
  have e : etaD d * (conj (etaD d) * z) = z := by rw [← mul_assoc, etaD_mul_conj, one_mul]
  rw [e, map_mul, conj_conj]
  simp only [mul_pow]
  ring

theorem sign_hermD (hd : 0 < d) (p q : ℕ) (h : p % d = q % d) :
    (-1 : ℂ) ^ (p % d + p / d) * (conj (etaD d) ^ p * etaD d ^ q)
      = (-1 : ℂ) ^ (q % d + q / d) := by
  have hcd : conj (etaD d) ^ d = -1 := by rw [← map_pow, etaD_pow hd, map_neg, map_one]
  have e1 : conj (etaD d) ^ p = conj (etaD d) ^ (p % d) * (-1 : ℂ) ^ (p / d) := by
    conv_lhs => rw [← Nat.mod_add_div p d]
    rw [pow_add, pow_mul, hcd]
  have e2 : etaD d ^ q = etaD d ^ (q % d) * (-1 : ℂ) ^ (q / d) := by
    conv_lhs => rw [← Nat.mod_add_div q d]
    rw [pow_add, pow_mul, etaD_pow hd]
  have hr : conj (etaD d) ^ (q % d) * etaD d ^ (q % d) = 1 := by
    rw [← mul_pow, mul_comm (conj (etaD d)) (etaD d), etaD_mul_conj, one_pow]
  have hs : ∀ m n : ℕ, (-1 : ℂ) ^ (n + 2 * m) = (-1 : ℂ) ^ n := fun m n => by
    rw [pow_add, pow_mul]; norm_num
  have hP : (-1 : ℂ) ^ (q % d + p / d) * (-1 : ℂ) ^ (p / d) * (-1 : ℂ) ^ (q / d)
      = (-1 : ℂ) ^ (q % d + q / d) := by
    rw [← pow_add, ← pow_add,
      show q % d + p / d + p / d + q / d = (q % d + q / d) + 2 * (p / d) by omega, hs]
  rw [e1, e2, h]
  linear_combination ((-1 : ℂ) ^ (q % d + p / d) * (-1 : ℂ) ^ (p / d) * (-1 : ℂ) ^ (q / d)) * hr
    + hP

theorem pairingD_X_pow_herm (hd : 0 < d) (a : ℝ) (p q : ℕ) :
    pairingD d a (X ^ p) (X ^ q) = conj (pairingD d a (X ^ q) (X ^ p)) := by
  by_cases h : p % d = q % d
  · rw [pairingD_X_pow hd a p q, pairingD_X_pow hd a q p, map_mul, map_pow, map_neg, map_one,
      conj_momentD hd a p q]
    linear_combination (-(∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z)) * sign_hermD hd p q h
  · rw [pairingD_X_pow_eq_zero hd a p q h, pairingD_X_pow_eq_zero hd a q p (fun h' => h h'.symm),
      map_zero]

theorem pairingD_herm (hd : 0 < d) (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    pairingD d a f g = conj (pairingD d a g f) := by
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 => rw [pairingD_add_left a ha, h1, h2, pairingD_add_right a ha g f1 f2, map_add]
  | monomial p c =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 => rw [pairingD_add_right a ha, h1, h2, pairingD_add_left a ha g1 g2, map_add]
    | monomial q b =>
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
      simp only [pairingD_C_mul_left, pairingD_C_mul_right, map_mul, conj_conj]
      rw [← pairingD_X_pow_herm hd a p q]
      ring

/-! ### Integration by parts -/

noncomputable def momD (d : ℕ) (a : ℝ) (p q : ℕ) : ℂ := ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z

noncomputable def ibpWD (d : ℕ) (a : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  ((p : ℂ) * z ^ (p - 1) * conj z ^ q + z ^ p * conj z ^ q * (-(a : ℂ) * conj z + I * z ^ (d - 1))) *
    densityD d a z

noncomputable def ibpVD (d : ℕ) (a : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  ((q : ℂ) * z ^ p * conj z ^ (q - 1) + z ^ p * conj z ^ q * (-(a : ℂ) * z + I * conj z ^ (d - 1))) *
    densityD d a z

lemma densityD_eq (a : ℝ) (z : ℂ) :
    densityD d a z = Complex.exp (-(a : ℂ) * (z * conj z) + (I / d) * (z ^ d + conj z ^ d)) := by
  unfold densityD; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma ibpWD_split (a : ℝ) (p q : ℕ) (z : ℂ) :
    ibpWD d a p q z = (p : ℂ) * (z ^ (p - 1) * conj z ^ q * densityD d a z) +
      I * (z ^ (p + (d - 1)) * conj z ^ q * densityD d a z) -
      (a : ℂ) * (z ^ p * conj z ^ (q + 1) * densityD d a z) := by
  unfold ibpWD; rw [pow_add, pow_succ]; ring

lemma ibpVD_split (a : ℝ) (p q : ℕ) (z : ℂ) :
    ibpVD d a p q z = (q : ℂ) * (z ^ p * conj z ^ (q - 1) * densityD d a z) -
      (a : ℂ) * (z ^ (p + 1) * conj z ^ q * densityD d a z) +
      I * (z ^ p * conj z ^ (q + (d - 1)) * densityD d a z) := by
  unfold ibpVD; rw [pow_add, pow_succ]; ring

lemma hasDerivAt_genD (hd : 0 < d) (a : ℝ) (p q : ℕ) (w c : ℝ → ℂ) (x : ℝ) (w' c' : ℂ)
    (hw : HasDerivAt w w' x) (hc : HasDerivAt c c' x) :
    HasDerivAt (fun t => w t ^ p * c t ^ q *
        Complex.exp (-(a : ℂ) * (w t * c t) + (I / d) * (w t ^ d + c t ^ d)))
      ((((p : ℂ) * w x ^ (p - 1) * w') * c x ^ q + w x ^ p * ((q : ℂ) * c x ^ (q - 1) * c')) *
          Complex.exp (-(a : ℂ) * (w x * c x) + (I / d) * (w x ^ d + c x ^ d)) +
        w x ^ p * c x ^ q * (Complex.exp (-(a : ℂ) * (w x * c x) + (I / d) * (w x ^ d + c x ^ d)) *
          (-(a : ℂ) * (w' * c x + w x * c') + I * (w x ^ (d - 1) * w' + c x ^ (d - 1) * c')))) x := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hD : HasDerivAt (fun t => w t ^ d + c t ^ d)
      ((d : ℂ) * w x ^ (d - 1) * w' + (d : ℂ) * c x ^ (d - 1) * c') x :=
    ((hw.pow d).add (hc.pow d)).congr_deriv (by simp)
  have hE : HasDerivAt (fun t => -(a : ℂ) * (w t * c t) + (I / d) * (w t ^ d + c t ^ d))
      (-(a : ℂ) * (w' * c x + w x * c') + I * (w x ^ (d - 1) * w' + c x ^ (d - 1) * c')) x := by
    refine (((hw.mul hc).const_mul (-(a : ℂ))).add (hD.const_mul (I / d))).congr_deriv ?_
    field_simp
  have h1 : HasDerivAt (fun t => w t ^ p * c t ^ q)
      ((p : ℂ) * w x ^ (p - 1) * w' * c x ^ q + w x ^ p * ((q : ℂ) * c x ^ (q - 1) * c')) x :=
    ((hw.pow p).mul (hc.pow q)).congr_deriv (by simp only [Pi.pow_apply])
  refine (h1.mul hE.cexp).congr_deriv ?_
  ring

lemma hasDerivAt_F_xD (hd : 0 < d) (a : ℝ) (p q : ℕ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ p * conj ((t : ℂ) + (y : ℂ) * I) ^ q *
        densityD d a ((t : ℂ) + (y : ℂ) * I))
      (ibpWD d a p q ((x : ℂ) + (y : ℂ) * I) + ibpVD d a p q ((x : ℂ) + (y : ℂ) * I)) x := by
  have hw : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ) - (y : ℂ) * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).sub_const ((y : ℂ) * I)
  have key := hasDerivAt_genD hd a p q (fun t : ℝ => (t : ℂ) + (y : ℂ) * I)
    (fun t : ℝ => (t : ℂ) - (y : ℂ) * I) x 1 1 hw hc
  have hfun : (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ p * conj ((t : ℂ) + (y : ℂ) * I) ^ q *
        densityD d a ((t : ℂ) + (y : ℂ) * I)) =
      (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ p * ((t : ℂ) - (y : ℂ) * I) ^ q *
        Complex.exp (-(a : ℂ) * (((t : ℂ) + (y : ℂ) * I) * ((t : ℂ) - (y : ℂ) * I)) +
          (I / d) * (((t : ℂ) + (y : ℂ) * I) ^ d + ((t : ℂ) - (y : ℂ) * I) ^ d))) := by
    funext t; rw [densityD_eq, conj_line]
  rw [hfun]
  refine key.congr_deriv ?_
  unfold ibpWD ibpVD
  rw [densityD_eq, conj_line]
  ring

lemma hasDerivAt_F_yD (hd : 0 < d) (a : ℝ) (p q : ℕ) (x y : ℝ) :
    HasDerivAt (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I) ^ p * conj ((x : ℂ) + (s : ℂ) * I) ^ q *
        densityD d a ((x : ℂ) + (s : ℂ) * I))
      (I * ibpWD d a p q ((x : ℂ) + (y : ℂ) * I) - I * ibpVD d a p q ((x : ℂ) + (y : ℂ) * I)) y := by
  have hw : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) I y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
  have hc : HasDerivAt (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) (-I) y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_sub (x : ℂ)
  have key := hasDerivAt_genD hd a p q (fun s : ℝ => (x : ℂ) + (s : ℂ) * I)
    (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) y I (-I) hw hc
  have hfun : (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I) ^ p * conj ((x : ℂ) + (s : ℂ) * I) ^ q *
        densityD d a ((x : ℂ) + (s : ℂ) * I)) =
      (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I) ^ p * ((x : ℂ) - (s : ℂ) * I) ^ q *
        Complex.exp (-(a : ℂ) * (((x : ℂ) + (s : ℂ) * I) * ((x : ℂ) - (s : ℂ) * I)) +
          (I / d) * (((x : ℂ) + (s : ℂ) * I) ^ d + ((x : ℂ) - (s : ℂ) * I) ^ d))) := by
    funext s; rw [densityD_eq, conj_line]
  rw [hfun]
  refine key.congr_deriv ?_
  unfold ibpWD ibpVD
  rw [densityD_eq, conj_line]
  ring

theorem momentD_ibp (hd : 0 < d) (a : ℝ) (ha : 0 < a) (p q : ℕ) :
    (p : ℂ) * momD d a (p - 1) q + I * momD d a (p + (d - 1)) q = (a : ℂ) * momD d a p (q + 1) := by
  have hG1 := integrable_momentD (d := d) a ha (p - 1) q
  have hG2 := integrable_momentD (d := d) a ha (p + (d - 1)) q
  have hG3 := integrable_momentD (d := d) a ha p (q + 1)
  have hH1 := integrable_momentD (d := d) a ha p (q - 1)
  have hH2 := integrable_momentD (d := d) a ha (p + 1) q
  have hH3 := integrable_momentD (d := d) a ha p (q + (d - 1))
  have hW : Integrable (ibpWD d a p q) := by
    have : (ibpWD d a p q) = fun z => (p : ℂ) * (z ^ (p - 1) * conj z ^ q * densityD d a z) +
        I * (z ^ (p + (d - 1)) * conj z ^ q * densityD d a z) -
        (a : ℂ) * (z ^ p * conj z ^ (q + 1) * densityD d a z) := funext (ibpWD_split a p q)
    rw [this]
    exact (((hG1.const_mul (p : ℂ)).add (hG2.const_mul I)).sub (hG3.const_mul (a : ℂ)))
  have hV : Integrable (ibpVD d a p q) := by
    have : (ibpVD d a p q) = fun z => (q : ℂ) * (z ^ p * conj z ^ (q - 1) * densityD d a z) -
        (a : ℂ) * (z ^ (p + 1) * conj z ^ q * densityD d a z) +
        I * (z ^ p * conj z ^ (q + (d - 1)) * densityD d a z) := funext (ibpVD_split a p q)
    rw [this]
    exact (((hH1.const_mul (q : ℂ)).sub (hH2.const_mul (a : ℂ))).add (hH3.const_mul I))
  have hfx : Integrable (fun z => ibpWD d a p q z + ibpVD d a p q z) := hW.add hV
  have hfy : Integrable (fun z => I * ibpWD d a p q z - I * ibpVD d a p q z) :=
    (hW.const_mul I).sub (hV.const_mul I)
  obtain ⟨h1, h2⟩ := ibp_core (fun z => z ^ p * conj z ^ q * densityD d a z)
    (fun z => ibpWD d a p q z + ibpVD d a p q z)
    (fun z => I * ibpWD d a p q z - I * ibpVD d a p q z)
    (hasDerivAt_F_xD hd a p q) (hasDerivAt_F_yD hd a p q) (integrable_momentD a ha p q) hfx hfy
  have hpt : ∀ z, 2 * ibpWD d a p q z =
      (ibpWD d a p q z + ibpVD d a p q z) - I * (I * ibpWD d a p q z - I * ibpVD d a p q z) :=
    fun z => by linear_combination (ibpWD d a p q z - ibpVD d a p q z) * Complex.I_sq
  have hW0 : ∫ z, ibpWD d a p q z = 0 := by
    have e1 : ∫ z, 2 * ibpWD d a p q z = ∫ z, ((ibpWD d a p q z + ibpVD d a p q z) -
        I * (I * ibpWD d a p q z - I * ibpVD d a p q z)) := by
      congr 1; funext z; exact hpt z
    rw [integral_const_mul] at e1
    rw [integral_sub hfx (hfy.const_mul I), integral_const_mul] at e1
    rw [h1, h2] at e1
    have : (2 : ℂ) * ∫ z, ibpWD d a p q z = 0 := by rw [e1]; ring
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have hsplit : ∫ z, ibpWD d a p q z = (p : ℂ) * momD d a (p - 1) q +
      I * momD d a (p + (d - 1)) q - (a : ℂ) * momD d a p (q + 1) := by
    unfold momD
    have e2 : ∫ z, ibpWD d a p q z = ∫ z, ((p : ℂ) * (z ^ (p - 1) * conj z ^ q * densityD d a z) +
        I * (z ^ (p + (d - 1)) * conj z ^ q * densityD d a z) -
        (a : ℂ) * (z ^ p * conj z ^ (q + 1) * densityD d a z)) := by
      congr 1; funext z; exact ibpWD_split a p q z
    have hA : Integrable (fun z : ℂ => (p : ℂ) * (z ^ (p - 1) * conj z ^ q * densityD d a z) +
        I * (z ^ (p + (d - 1)) * conj z ^ q * densityD d a z)) :=
      (hG1.const_mul (p : ℂ)).add (hG2.const_mul I)
    have hB : Integrable (fun z : ℂ => (a : ℂ) * (z ^ p * conj z ^ (q + 1) * densityD d a z)) :=
      hG3.const_mul (a : ℂ)
    rw [e2, integral_sub hA hB, integral_add (hG1.const_mul (p : ℂ)) (hG2.const_mul I),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsplit] at hW0
  linear_combination hW0

/-- `ε(n) = -τ(n) ε(n+1)` for `ε(n) = (-1)^{n mod d + ⌊n/d⌋}`. -/
lemma sign_stepD (hd : 0 < d) (n : ℕ) :
    (-1 : ℂ) ^ (n % d + n / d) = -(tauD d n : ℂ) * (-1 : ℂ) ^ ((n + 1) % d + (n + 1) / d) := by
  have h1 := rhoSignD_eq hd n
  have h2 := rhoSignD_eq hd (n + 1)
  have hstep : rhoSignD d (n + 1) = -tauD d n * rhoSignD d n := by
    unfold rhoSignD; rw [Finset.prod_range_succ]; ring
  have hτ : tauD d n * tauD d n = 1 := by
    unfold tauD
    split_ifs
    · rw [← mul_pow]; norm_num
    · norm_num
  have : (-1 : ℝ) ^ (n % d + n / d) = -tauD d n * (-1 : ℝ) ^ ((n + 1) % d + (n + 1) / d) := by
    rw [← h1, ← h2, hstep]
    linear_combination (-rhoSignD d n) * hτ
  exact_mod_cast this

/-- **Integration by parts** in pairing form (`eq:ibp-pairing`). -/
theorem pairingD_ibp (hd : 0 < d) (a : ℝ) (ha : 0 < a) (f : ℂ[X]) (q : ℕ) :
    pairingD d a (derivative f + C I * X ^ (d - 1) * f) (X ^ q) =
      -(tauD d q : ℂ) * a * pairingD d a f (X ^ (q + 1)) := by
  have hX : ∀ n : ℕ, pairingD d a (derivative (X ^ n) + C I * X ^ (d - 1) * X ^ n) (X ^ q)
      = -(tauD d q : ℂ) * a * pairingD d a (X ^ n) (X ^ (q + 1)) := by
    intro n
    have e1 : C I * X ^ (d - 1) * X ^ n = C I * X ^ (n + (d - 1)) := by ring
    rw [derivative_X_pow, e1, pairingD_add_left a ha]
    simp only [pairingD_C_mul_left]
    rw [pairingD_X_pow hd a (n - 1) q, pairingD_X_pow hd a (n + (d - 1)) q,
      pairingD_X_pow hd a n (q + 1)]
    have hm := momentD_ibp hd a ha n q
    unfold momD at hm
    linear_combination (-1 : ℂ) ^ (q % d + q / d) * hm
      + ((a : ℂ) * ∫ z : ℂ, z ^ n * conj z ^ (q + 1) * densityD d a z) * sign_stepD hd q
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 =>
    have e : derivative (f1 + f2) + C I * X ^ (d - 1) * (f1 + f2)
        = (derivative f1 + C I * X ^ (d - 1) * f1) + (derivative f2 + C I * X ^ (d - 1) * f2) := by
      rw [derivative_add]; ring
    rw [e, pairingD_add_left a ha, h1, h2, pairingD_add_left a ha f1 f2 (X ^ (q + 1))]
    ring
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    have e : derivative (C c * X ^ n) + C I * X ^ (d - 1) * (C c * X ^ n)
        = C c * (derivative (X ^ n) + C I * X ^ (d - 1) * X ^ n) := by
      rw [derivative_C_mul]; ring
    rw [e, pairingD_C_mul_left, pairingD_C_mul_left, hX n]
    ring

end Painleve
