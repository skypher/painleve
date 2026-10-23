import Painleve.Moments
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Complex.Norm

namespace Painleve
open Complex MeasureTheory
open scoped ComplexConjugate

/-- The moment ∫ z^p conj(z)^q ρ_a. -/
noncomputable def mom (a : ℝ) (p q : ℕ) : ℂ := ∫ z : ℂ, z ^ p * conj z ^ q * density a z

/-- Integrand of the x-derivative combination `∂_x - i ∂_y` applied to `z^p conj z^q ρ_a`,
divided by two (that is `∂_z`). -/
noncomputable def ibpW (a : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  ((p : ℂ) * z ^ (p - 1) * conj z ^ q + z ^ p * conj z ^ q * (-(a : ℂ) * conj z + I * z ^ 3)) *
    density a z

/-- Integrand of `∂_{conj z}` applied to `z^p conj z^q ρ_a`, times two. -/
noncomputable def ibpV (a : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  ((q : ℂ) * z ^ p * conj z ^ (q - 1) + z ^ p * conj z ^ q * (-(a : ℂ) * z + I * conj z ^ 3)) *
    density a z

lemma density_eq (a : ℝ) (z : ℂ) :
    density a z = Complex.exp (-(a : ℂ) * (z * conj z) + (I / 4) * (z ^ 4 + conj z ^ 4)) := by
  unfold density
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma conj_line (x y : ℝ) : conj ((x : ℂ) + (y : ℂ) * I) = (x : ℂ) - (y : ℂ) * I := by
  simp only [map_add, map_mul, conj_ofReal, conj_I]
  ring

lemma ibpW_split (a : ℝ) (p q : ℕ) (z : ℂ) :
    ibpW a p q z = (p : ℂ) * (z ^ (p - 1) * conj z ^ q * density a z) +
      I * (z ^ (p + 3) * conj z ^ q * density a z) -
      (a : ℂ) * (z ^ p * conj z ^ (q + 1) * density a z) := by
  unfold ibpW
  ring

lemma ibpV_split (a : ℝ) (p q : ℕ) (z : ℂ) :
    ibpV a p q z = (q : ℂ) * (z ^ p * conj z ^ (q - 1) * density a z) -
      (a : ℂ) * (z ^ (p + 1) * conj z ^ q * density a z) +
      I * (z ^ p * conj z ^ (q + 3) * density a z) := by
  unfold ibpV
  ring

/-- Chain rule for `w(t)^p c(t)^q exp(E(w(t), c(t)))` with `E(w, c) = -a w c + (i/4)(w⁴ + c⁴)`. -/
lemma hasDerivAt_gen (a : ℝ) (p q : ℕ) (w c : ℝ → ℂ) (x : ℝ) (w' c' : ℂ)
    (hw : HasDerivAt w w' x) (hc : HasDerivAt c c' x) :
    HasDerivAt (fun t => w t ^ p * c t ^ q *
        Complex.exp (-(a : ℂ) * (w t * c t) + (I / 4) * (w t ^ 4 + c t ^ 4)))
      ((((p : ℂ) * w x ^ (p - 1) * w') * c x ^ q + w x ^ p * ((q : ℂ) * c x ^ (q - 1) * c')) *
          Complex.exp (-(a : ℂ) * (w x * c x) + (I / 4) * (w x ^ 4 + c x ^ 4)) +
        w x ^ p * c x ^ q * (Complex.exp (-(a : ℂ) * (w x * c x) + (I / 4) * (w x ^ 4 + c x ^ 4)) *
          (-(a : ℂ) * (w' * c x + w x * c') + (I / 4) * (4 * w x ^ 3 * w' + 4 * c x ^ 3 * c')))) x := by
  have h4 : HasDerivAt (fun t => w t ^ 4 + c t ^ 4) (4 * w x ^ 3 * w' + 4 * c x ^ 3 * c') x :=
    ((hw.pow 4).add (hc.pow 4)).congr_deriv (by norm_num)
  have hE : HasDerivAt (fun t => -(a : ℂ) * (w t * c t) + (I / 4) * (w t ^ 4 + c t ^ 4))
      (-(a : ℂ) * (w' * c x + w x * c') + (I / 4) * (4 * w x ^ 3 * w' + 4 * c x ^ 3 * c')) x :=
    ((hw.mul hc).const_mul (-(a : ℂ))).add (h4.const_mul (I / 4))
  have h1 : HasDerivAt (fun t => w t ^ p * c t ^ q)
      ((p : ℂ) * w x ^ (p - 1) * w' * c x ^ q + w x ^ p * ((q : ℂ) * c x ^ (q - 1) * c')) x :=
    ((hw.pow p).mul (hc.pow q)).congr_deriv (by simp only [Pi.pow_apply])
  refine (h1.mul hE.cexp).congr_deriv ?_
  ring

lemma hasDerivAt_F_x (a : ℝ) (p q : ℕ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ p * conj ((t : ℂ) + (y : ℂ) * I) ^ q *
        density a ((t : ℂ) + (y : ℂ) * I))
      (ibpW a p q ((x : ℂ) + (y : ℂ) * I) + ibpV a p q ((x : ℂ) + (y : ℂ) * I)) x := by
  have hw : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ) - (y : ℂ) * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).sub_const ((y : ℂ) * I)
  have key := hasDerivAt_gen a p q (fun t : ℝ => (t : ℂ) + (y : ℂ) * I)
    (fun t : ℝ => (t : ℂ) - (y : ℂ) * I) x 1 1 hw hc
  have hfun : (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ p * conj ((t : ℂ) + (y : ℂ) * I) ^ q *
        density a ((t : ℂ) + (y : ℂ) * I)) =
      (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ p * ((t : ℂ) - (y : ℂ) * I) ^ q *
        Complex.exp (-(a : ℂ) * (((t : ℂ) + (y : ℂ) * I) * ((t : ℂ) - (y : ℂ) * I)) +
          (I / 4) * (((t : ℂ) + (y : ℂ) * I) ^ 4 + ((t : ℂ) - (y : ℂ) * I) ^ 4))) := by
    funext t
    rw [density_eq, conj_line]
  rw [hfun]
  refine key.congr_deriv ?_
  unfold ibpW ibpV
  rw [density_eq, conj_line]
  ring

lemma hasDerivAt_F_y (a : ℝ) (p q : ℕ) (x y : ℝ) :
    HasDerivAt (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I) ^ p * conj ((x : ℂ) + (s : ℂ) * I) ^ q *
        density a ((x : ℂ) + (s : ℂ) * I))
      (I * ibpW a p q ((x : ℂ) + (y : ℂ) * I) - I * ibpV a p q ((x : ℂ) + (y : ℂ) * I)) y := by
  have hw : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) I y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
  have hc : HasDerivAt (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) (-I) y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_sub (x : ℂ)
  have key := hasDerivAt_gen a p q (fun s : ℝ => (x : ℂ) + (s : ℂ) * I)
    (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) y I (-I) hw hc
  have hfun : (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I) ^ p * conj ((x : ℂ) + (s : ℂ) * I) ^ q *
        density a ((x : ℂ) + (s : ℂ) * I)) =
      (fun s : ℝ => ((x : ℂ) + (s : ℂ) * I) ^ p * ((x : ℂ) - (s : ℂ) * I) ^ q *
        Complex.exp (-(a : ℂ) * (((x : ℂ) + (s : ℂ) * I) * ((x : ℂ) - (s : ℂ) * I)) +
          (I / 4) * (((x : ℂ) + (s : ℂ) * I) ^ 4 + ((x : ℂ) - (s : ℂ) * I) ^ 4))) := by
    funext s
    rw [density_eq, conj_line]
  rw [hfun]
  refine key.congr_deriv ?_
  unfold ibpW ibpV
  rw [density_eq, conj_line]
  ring

/-- Fubini in the first real variable: a derivative in `x` integrates to zero. -/
lemma integral_fst_deriv_zero (Φ D : ℝ × ℝ → ℂ)
    (hΦ : ∀ x y : ℝ, HasDerivAt (fun t => Φ (t, y)) (D (x, y)) x)
    (hD : Integrable D (volume : Measure (ℝ × ℝ))) (hΦi : Integrable Φ (volume : Measure (ℝ × ℝ))) :
    ∫ p, D p = 0 := by
  rw [Measure.volume_eq_prod ℝ ℝ] at hD hΦi ⊢
  rw [integral_prod_symm D hD]
  have hae : (fun y : ℝ => ∫ x, D (x, y)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hD.prod_left_ae, hΦi.prod_left_ae] with y h1 h2
    exact integral_eq_zero_of_hasDerivAt_of_integrable (f := fun t => Φ (t, y))
      (f' := fun x => D (x, y)) (fun x => hΦ x y) h1 h2
  rw [integral_congr_ae hae, integral_zero]

/-- Fubini in the second real variable: a derivative in `y` integrates to zero. -/
lemma integral_snd_deriv_zero (Φ D : ℝ × ℝ → ℂ)
    (hΦ : ∀ x y : ℝ, HasDerivAt (fun t => Φ (x, t)) (D (x, y)) y)
    (hD : Integrable D (volume : Measure (ℝ × ℝ))) (hΦi : Integrable Φ (volume : Measure (ℝ × ℝ))) :
    ∫ p, D p = 0 := by
  rw [Measure.volume_eq_prod ℝ ℝ] at hD hΦi ⊢
  rw [integral_prod D hD]
  have hae : (fun x : ℝ => ∫ y, D (x, y)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hD.prod_right_ae, hΦi.prod_right_ae] with x h1 h2
    exact integral_eq_zero_of_hasDerivAt_of_integrable (f := fun t => Φ (x, t))
      (f' := fun y => D (x, y)) (fun y => hΦ x y) h1 h2
  rw [integral_congr_ae hae, integral_zero]

/-- Core Fubini step on `ℂ`: the two real partial derivatives integrate to zero. -/
lemma ibp_core (f fx fy : ℂ → ℂ)
    (hx : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => f ((t : ℂ) + (y : ℂ) * I))
      (fx ((x : ℂ) + (y : ℂ) * I)) x)
    (hy : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => f ((x : ℂ) + (t : ℂ) * I))
      (fy ((x : ℂ) + (y : ℂ) * I)) y)
    (hf : Integrable f) (hfx : Integrable fx) (hfy : Integrable fy) :
    ∫ z, fx z = 0 ∧ ∫ z, fy z = 0 := by
  let e := Complex.measurableEquivRealProd
  have hmp : MeasurePreserving e.symm volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm e
  have hpsi : ∀ p : ℝ × ℝ, e.symm p = (p.1 : ℂ) + (p.2 : ℂ) * I := fun p => by
    rw [Complex.measurableEquivRealProd_symm_apply]
    exact Complex.mk_eq_add_mul_I _ _
  have hT : ∀ g : ℂ → ℂ, ∫ z, g z = ∫ p : ℝ × ℝ, g (e.symm p) := fun g =>
    (hmp.integral_comp' g).symm
  have hI : ∀ g : ℂ → ℂ, Integrable g → Integrable (fun p : ℝ × ℝ => g (e.symm p)) :=
    fun g hg => (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hg
  have h1 : ∫ p : ℝ × ℝ, fx (e.symm p) = 0 := by
    refine integral_fst_deriv_zero (fun p => f (e.symm p)) (fun p => fx (e.symm p)) ?_
      (hI fx hfx) (hI f hf)
    intro x y
    have := hx x y
    simp only [hpsi]
    exact this
  have h2 : ∫ p : ℝ × ℝ, fy (e.symm p) = 0 := by
    refine integral_snd_deriv_zero (fun p => f (e.symm p)) (fun p => fy (e.symm p)) ?_
      (hI fy hfy) (hI f hf)
    intro x y
    have := hy x y
    simp only [hpsi]
    exact this
  exact ⟨by rw [hT fx]; exact h1, by rw [hT fy]; exact h2⟩

theorem moment_ibp (a : ℝ) (ha : 0 < a) (p q : ℕ) :
    (p : ℂ) * mom a (p - 1) q + I * mom a (p + 3) q = (a : ℂ) * mom a p (q + 1) := by
  have hG1 := integrable_moment a ha (p - 1) q
  have hG2 := integrable_moment a ha (p + 3) q
  have hG3 := integrable_moment a ha p (q + 1)
  have hH1 := integrable_moment a ha p (q - 1)
  have hH2 := integrable_moment a ha (p + 1) q
  have hH3 := integrable_moment a ha p (q + 3)
  have hW : Integrable (ibpW a p q) := by
    have : (ibpW a p q) = fun z => (p : ℂ) * (z ^ (p - 1) * conj z ^ q * density a z) +
        I * (z ^ (p + 3) * conj z ^ q * density a z) -
        (a : ℂ) * (z ^ p * conj z ^ (q + 1) * density a z) := funext (ibpW_split a p q)
    rw [this]
    exact (((hG1.const_mul (p : ℂ)).add (hG2.const_mul I)).sub (hG3.const_mul (a : ℂ)))
  have hV : Integrable (ibpV a p q) := by
    have : (ibpV a p q) = fun z => (q : ℂ) * (z ^ p * conj z ^ (q - 1) * density a z) -
        (a : ℂ) * (z ^ (p + 1) * conj z ^ q * density a z) +
        I * (z ^ p * conj z ^ (q + 3) * density a z) := funext (ibpV_split a p q)
    rw [this]
    exact (((hH1.const_mul (q : ℂ)).sub (hH2.const_mul (a : ℂ))).add (hH3.const_mul I))
  have hfx : Integrable (fun z => ibpW a p q z + ibpV a p q z) := hW.add hV
  have hfy : Integrable (fun z => I * ibpW a p q z - I * ibpV a p q z) :=
    (hW.const_mul I).sub (hV.const_mul I)
  obtain ⟨h1, h2⟩ := ibp_core (fun z => z ^ p * conj z ^ q * density a z)
    (fun z => ibpW a p q z + ibpV a p q z) (fun z => I * ibpW a p q z - I * ibpV a p q z)
    (hasDerivAt_F_x a p q) (hasDerivAt_F_y a p q) (integrable_moment a ha p q) hfx hfy
  have hpt : ∀ z, 2 * ibpW a p q z =
      (ibpW a p q z + ibpV a p q z) - I * (I * ibpW a p q z - I * ibpV a p q z) := fun z => by
    linear_combination (ibpW a p q z - ibpV a p q z) * Complex.I_sq
  have hW0 : ∫ z, ibpW a p q z = 0 := by
    have e1 : ∫ z, 2 * ibpW a p q z = ∫ z, ((ibpW a p q z + ibpV a p q z) -
        I * (I * ibpW a p q z - I * ibpV a p q z)) := by
      congr 1
      funext z
      exact hpt z
    rw [integral_const_mul] at e1
    rw [integral_sub hfx (hfy.const_mul I), integral_const_mul] at e1
    rw [h1, h2] at e1
    have : (2 : ℂ) * ∫ z, ibpW a p q z = 0 := by rw [e1]; ring
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have hsplit : ∫ z, ibpW a p q z = (p : ℂ) * mom a (p - 1) q + I * mom a (p + 3) q -
      (a : ℂ) * mom a p (q + 1) := by
    unfold mom
    have e2 : ∫ z, ibpW a p q z = ∫ z, ((p : ℂ) * (z ^ (p - 1) * conj z ^ q * density a z) +
        I * (z ^ (p + 3) * conj z ^ q * density a z) -
        (a : ℂ) * (z ^ p * conj z ^ (q + 1) * density a z)) := by
      congr 1
      funext z
      exact ibpW_split a p q z
    have hA : Integrable (fun z : ℂ => (p : ℂ) * (z ^ (p - 1) * conj z ^ q * density a z) +
        I * (z ^ (p + 3) * conj z ^ q * density a z)) :=
      (hG1.const_mul (p : ℂ)).add (hG2.const_mul I)
    have hB : Integrable (fun z : ℂ => (a : ℂ) * (z ^ p * conj z ^ (q + 1) * density a z)) :=
      hG3.const_mul (a : ℂ)
    rw [e2, integral_sub hA hB, integral_add (hG1.const_mul (p : ℂ)) (hG2.const_mul I),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsplit] at hW0
  linear_combination hW0

end Painleve
