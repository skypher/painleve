import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set

namespace Painleve

/-- Integrand after the substitution `σ = x²`. -/
noncomputable def subordH (p q x : ℝ) : ℝ := Real.exp (-(p * x ^ 2) - q / x ^ 2)

lemma subord_image_sub (c : ℝ) (hc : 0 < c) :
    (fun t : ℝ => t - c / t) '' Ioi 0 = univ := by
  refine Set.eq_univ_of_forall fun u => ?_
  have hs0 : 0 ≤ Real.sqrt (u ^ 2 + 4 * c) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (u ^ 2 + 4 * c) ^ 2 = u ^ 2 + 4 * c :=
    Real.sq_sqrt (by positivity)
  set s := Real.sqrt (u ^ 2 + 4 * c) with hs_def
  have hpos : 0 < u + s := by nlinarith
  have ht : (u + s) / 2 ≠ 0 := (div_pos hpos two_pos).ne'
  have h1 : c / ((u + s) / 2) = (s - u) / 2 := by
    rw [div_eq_iff ht]
    linear_combination (-1 / 4 : ℝ) * hs2
  refine ⟨(u + s) / 2, div_pos hpos two_pos, ?_⟩
  show (u + s) / 2 - c / ((u + s) / 2) = u
  rw [h1]
  ring

lemma subord_injOn_sub (c : ℝ) (hc : 0 < c) : InjOn (fun t : ℝ => t - c / t) (Ioi 0) := by
  intro t1 h1 t2 h2 heq
  have h1' : (0 : ℝ) < t1 := h1
  have h2' : (0 : ℝ) < t2 := h2
  have heq' : t1 - c / t1 = t2 - c / t2 := heq
  have k1 : t1 * (c / t1) = c := by field_simp
  have k2 : t2 * (c / t2) = c := by field_simp
  have key : (t1 - t2) * (t1 * t2 + c) = 0 := by
    linear_combination (t1 * t2) * heq' + t2 * k1 - t1 * k2
  rcases mul_eq_zero.mp key with h | h
  · linarith
  · nlinarith [mul_pos h1' h2']

lemma subord_injOn_inv (c : ℝ) (hc : 0 < c) : InjOn (fun t : ℝ => c / t) (Ioi 0) := by
  intro t1 h1 t2 h2 heq
  have h1' : (0 : ℝ) < t1 := h1
  have h2' : (0 : ℝ) < t2 := h2
  have heq' : c / t1 = c / t2 := heq
  have e : c * t2 = c * t1 := (div_eq_div_iff h1'.ne' h2'.ne').mp heq'
  exact (mul_left_cancel₀ hc.ne' e).symm

lemma subord_image_inv (c : ℝ) (hc : 0 < c) : (fun t : ℝ => c / t) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact div_pos hc ht
  · intro hy
    have hy' : (0 : ℝ) < y := hy
    have hyne : y ≠ 0 := hy'.ne'
    have hcne : c ≠ 0 := hc.ne'
    exact ⟨c / y, div_pos hc hy', by field_simp⟩

lemma subord_hasDeriv_sub (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t - c / t) (1 + c / x ^ 2) x := by
  have h : HasDerivAt (fun t : ℝ => t - c * t⁻¹) (1 - c * -(x ^ 2)⁻¹) x :=
    (hasDerivAt_id' x).sub ((hasDerivAt_inv hx.ne').const_mul c)
  have e : (fun t : ℝ => t - c / t) = (fun t : ℝ => t - c * t⁻¹) := by
    funext t
    ring
  rw [e]
  exact h.congr_deriv (by ring)

lemma subord_hasDeriv_inv (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => c / t) (-(c / x ^ 2)) x := by
  have h : HasDerivAt (fun t : ℝ => c * t⁻¹) (c * -(x ^ 2)⁻¹) x :=
    (hasDerivAt_inv hx.ne').const_mul c
  have e : (fun t : ℝ => c / t) = (fun t : ℝ => c * t⁻¹) := by
    funext t
    ring
  rw [e]
  exact h.congr_deriv (by ring)

lemma subord_symm (p q c : ℝ) (hpc : p * c ^ 2 = q) {x : ℝ} (hx : 0 < x) (hc : 0 < c) :
    subordH p q (c / x) = subordH p q x := by
  subst hpc
  have hxne : x ≠ 0 := hx.ne'
  have hcne : c ≠ 0 := hc.ne'
  unfold subordH
  congr 1
  field_simp
  ring

lemma subord_factor (p q c : ℝ) (hpc : p * c ^ 2 = q) {x : ℝ} (hx : 0 < x) (hc : 0 < c) :
    subordH p q x = Real.exp (-(2 * (p * c))) * Real.exp (-(p * (x - c / x) ^ 2)) := by
  subst hpc
  have hxne : x ≠ 0 := hx.ne'
  have hcne : c ≠ 0 := hc.ne'
  rw [← Real.exp_add]
  unfold subordH
  congr 1
  field_simp
  ring

lemma subord_sqrt (p q c : ℝ) (hp : 0 < p) (hc : 0 < c) (hpc : p * c ^ 2 = q) :
    Real.sqrt (p * q) = p * c := by
  rw [← hpc, show p * (p * c ^ 2) = (p * c) ^ 2 by ring]
  exact Real.sqrt_sq (mul_pos hp hc).le

lemma subord_gauss (p c : ℝ) (hc : 0 < c) :
    ∫ u : ℝ, Real.exp (-p * u ^ 2) =
      ∫ x in Ioi (0 : ℝ), (1 + c / x ^ 2) * Real.exp (-(p * (x - c / x) ^ 2)) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun t : ℝ => t - c / t)
    (f' := fun x => 1 + c / x ^ 2) measurableSet_Ioi
    (fun x hx => (subord_hasDeriv_sub c (mem_Ioi.mp hx)).hasDerivWithinAt)
    (subord_injOn_sub c hc) (fun u : ℝ => Real.exp (-p * u ^ 2))
  rw [subord_image_sub c hc, Measure.restrict_univ] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx' : 0 < x := hx
  have hpos : 0 < 1 + c / x ^ 2 := by
    have := div_pos hc (pow_pos hx' 2)
    linarith
  simp only [smul_eq_mul, neg_mul]
  rw [abs_of_pos hpos]

lemma subord_sym_int (p q c : ℝ) (hc : 0 < c) (hpc : p * c ^ 2 = q) :
    ∫ x in Ioi (0 : ℝ), subordH p q x = ∫ x in Ioi (0 : ℝ), (c / x ^ 2) * subordH p q x := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun t : ℝ => c / t)
    (f' := fun x => -(c / x ^ 2)) measurableSet_Ioi
    (fun x hx => (subord_hasDeriv_inv c (mem_Ioi.mp hx)).hasDerivWithinAt)
    (subord_injOn_inv c hc) (subordH p q)
  rw [subord_image_inv c hc] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx' : 0 < x := hx
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (div_pos hc (pow_pos hx' 2)), subord_symm p q c hpc hx' hc]

lemma subord_int_H (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (subordH p q) (Ioi 0) := by
  refine Integrable.mono' (integrable_exp_neg_mul_sq hp).integrableOn ?_ ?_
  · have : Measurable (subordH p q) := by
      unfold subordH
      fun_prop
    exact this.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : 0 < x := hx
    unfold subordH
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ q / x ^ 2 := div_nonneg hq.le (sq_nonneg x)
    rw [neg_mul]
    linarith

lemma subord_int_W (p q c : ℝ) (hc : 0 < c) (hpc : p * c ^ 2 = q)
    (hint : IntegrableOn (subordH p q) (Ioi 0)) :
    IntegrableOn (fun x => (c / x ^ 2) * subordH p q x) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun t : ℝ => c / t)
    (f' := fun x => -(c / x ^ 2)) measurableSet_Ioi
    (fun x hx => (subord_hasDeriv_inv c (mem_Ioi.mp hx)).hasDerivWithinAt)
    (subord_injOn_inv c hc) (subordH p q)
  rw [subord_image_inv c hc] at h
  refine (h.mp hint).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx' : 0 < x := hx
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (div_pos hc (pow_pos hx' 2)), subord_symm p q c hpc hx' hc]

theorem subordination (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∫ σ in Set.Ioi (0:ℝ), σ ^ (-(1/2 : ℝ)) * Real.exp (-(p * σ) - q / σ) =
      Real.sqrt (Real.pi / p) * Real.exp (-2 * Real.sqrt (p * q)) := by
  obtain ⟨c, hc, hpc⟩ : ∃ c : ℝ, 0 < c ∧ p * c ^ 2 = q :=
    ⟨Real.sqrt (q / p), Real.sqrt_pos.mpr (div_pos hq hp), by
      rw [Real.sq_sqrt (div_pos hq hp).le]; field_simp⟩
  -- Step 1: substitution σ = x²
  have step1 : ∫ σ in Set.Ioi (0:ℝ), σ ^ (-(1/2 : ℝ)) * Real.exp (-(p * σ) - q / σ) =
      2 * ∫ x in Ioi (0 : ℝ), subordH p q x := by
    have h := integral_comp_rpow_Ioi_of_pos
      (g := fun σ : ℝ => σ ^ (-(1/2 : ℝ)) * Real.exp (-(p * σ) - q / σ)) (p := (2 : ℝ)) two_pos
    have hpt : ∀ x ∈ Ioi (0 : ℝ),
        (2 * x ^ ((2 : ℝ) - 1)) • ((x ^ (2 : ℝ)) ^ (-(1/2 : ℝ)) *
          Real.exp (-(p * x ^ (2 : ℝ)) - q / x ^ (2 : ℝ))) = 2 * subordH p q x := by
      intro x hx
      have hx0 : 0 < x := hx
      have hxne : x ≠ 0 := hx0.ne'
      have hxp : (x ^ (2 : ℝ)) ^ (-(1/2 : ℝ)) = x⁻¹ := by
        rw [← Real.rpow_mul hx0.le, show (2 : ℝ) * -(1/2) = -1 by norm_num, Real.rpow_neg_one]
      have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
      rw [hxp, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, smul_eq_mul]
      unfold subordH
      linear_combination (2 * Real.exp (-(p * x ^ 2) - q / x ^ 2)) * hinv
    calc ∫ σ in Ioi (0:ℝ), σ ^ (-(1/2 : ℝ)) * Real.exp (-(p * σ) - q / σ)
        = ∫ x in Ioi (0:ℝ), (2 * x ^ ((2 : ℝ) - 1)) • ((x ^ (2 : ℝ)) ^ (-(1/2 : ℝ)) *
            Real.exp (-(p * x ^ (2 : ℝ)) - q / x ^ (2 : ℝ))) := h.symm
      _ = ∫ x in Ioi (0:ℝ), 2 * subordH p q x :=
          setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpt x hx)
      _ = 2 * ∫ x in Ioi (0:ℝ), subordH p q x := integral_const_mul _ _
  -- Step 2: symmetry, Gaussian, and splitting
  have hint := subord_int_H p q hp hq
  have hW := subord_int_W p q c hc hpc hint
  have hsym := subord_sym_int p q c hc hpc
  have hG := subord_gauss p c hc
  have hgauss : ∫ u : ℝ, Real.exp (-p * u ^ 2) = Real.sqrt (Real.pi / p) := integral_gaussian p
  have hsplit : ∫ x in Ioi (0:ℝ), (1 + c / x ^ 2) * subordH p q x =
      (∫ x in Ioi (0:ℝ), subordH p q x) + ∫ x in Ioi (0:ℝ), (c / x ^ 2) * subordH p q x := by
    rw [← integral_add hint hW]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    ring
  have hE : ∫ x in Ioi (0:ℝ), (1 + c / x ^ 2) * subordH p q x =
      Real.exp (-(2 * (p * c))) * Real.sqrt (Real.pi / p) := by
    have h5 : ∫ x in Ioi (0:ℝ), (1 + c / x ^ 2) * subordH p q x =
        ∫ x in Ioi (0:ℝ), Real.exp (-(2 * (p * c))) *
          ((1 + c / x ^ 2) * Real.exp (-(p * (x - c / x) ^ 2))) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
        rw [subord_factor p q c hpc (mem_Ioi.mp hx) hc]
        ring)
    rw [h5, integral_const_mul, ← hG, hgauss]
  have h3 : (∫ x in Ioi (0:ℝ), subordH p q x) + ∫ x in Ioi (0:ℝ), (c / x ^ 2) * subordH p q x =
      Real.exp (-(2 * (p * c))) * Real.sqrt (Real.pi / p) := by
    rw [← hsplit, hE]
  rw [← hsym] at h3
  have hexp : Real.exp (-2 * Real.sqrt (p * q)) = Real.exp (-(2 * (p * c))) := by
    rw [subord_sqrt p q c hp hc hpc]
    congr 1
    ring
  rw [step1, hexp]
  linear_combination h3

end Painleve
