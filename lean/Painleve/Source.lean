import Painleve.Subord
import Painleve.Moments
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Complex MeasureTheory Set
open scoped ComplexConjugate
open Real

namespace Painleve

lemma hasFDerivAt_sq (z : ℂ) :
    HasFDerivAt (fun w : ℂ => w ^ 2) (ContinuousLinearMap.mul ℝ ℂ (2 * z)) z := by
  have h : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h2 := h.hasFDerivAt.restrictScalars ℝ
  have key : (ContinuousLinearMap.mul ℝ ℂ (2 * z)) =
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * z)).restrictScalars ℝ) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [mul_comm]
  rw [key]
  exact h2

lemma det_mul_two (z : ℂ) :
    (ContinuousLinearMap.mul ℝ ℂ (2 * z)).det = 4 * ‖z‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [LinearMap.toMatrix_apply, Complex.basisOneI]
  ring

lemma sq_injOn_pos : InjOn (fun w : ℂ => w ^ 2) {z : ℂ | 0 < z.re} := by
  intro z1 h1 z2 h2 e
  have h1' : 0 < z1.re := h1
  have h2' : 0 < z2.re := h2
  have e' : (z1 - z2) * (z1 + z2) = 0 := by
    have : z1 ^ 2 - z2 ^ 2 = 0 := sub_eq_zero.mpr e
    linear_combination this
  rcases mul_eq_zero.mp e' with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp at hre
    linarith

lemma sq_injOn_neg : InjOn (fun w : ℂ => w ^ 2) {z : ℂ | z.re < 0} := by
  intro z1 h1 z2 h2 e
  have h1' : z1.re < 0 := h1
  have h2' : z2.re < 0 := h2
  have e' : (z1 - z2) * (z1 + z2) = 0 := by
    have : z1 ^ 2 - z2 ^ 2 = 0 := sub_eq_zero.mpr e
    linear_combination this
  rcases mul_eq_zero.mp e' with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp at hre
    linarith

lemma sq_image_pos_subset (z : ℂ) (hz : 0 < z.re) : z ^ 2 ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff, pow_two, Complex.mul_re, Complex.mul_im]
  by_cases h : z.re * z.im + z.im * z.re = 0
  · left
    have h0 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · have : z.re * z.re > 0 := mul_pos hz hz
      rw [h1]
      nlinarith
  · right
    exact h

lemma sq_image_neg_subset (z : ℂ) (hz : z.re < 0) : z ^ 2 ∈ slitPlane := by
  have hz' : 0 < (-z).re := by simp; linarith
  have := sq_image_pos_subset (-z) hz'
  simpa using this

/-- Every point of the slit plane is a square of a point with positive real part. -/
lemma exists_sqrt_pos_re (w : ℂ) (hw : w ∈ slitPlane) :
    ∃ z : ℂ, 0 < z.re ∧ z ^ 2 = w := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hhalf : ((2 : ℕ) : ℂ)⁻¹ = (1 / 2 : ℂ) := by norm_num
  refine ⟨w ^ (((2 : ℕ) : ℂ)⁻¹), ?_, ?_⟩
  · have harg : w.arg ≠ Real.pi := slitPlane_arg_ne_pi hw
    have hlt : w.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi w) harg
    have hgt : -Real.pi < w.arg := Complex.neg_pi_lt_arg w
    rw [hhalf, Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
    apply mul_pos (Real.exp_pos _)
    apply Real.cos_pos_of_mem_Ioo
    have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
      simp [Complex.log_im, div_eq_mul_inv]
    rw [him]
    constructor <;> linarith
  · exact Complex.cpow_nat_inv_pow w (by norm_num)



lemma sq_image_pos : (fun w : ℂ => w ^ 2) '' {z : ℂ | 0 < z.re} = slitPlane := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact sq_image_pos_subset z hz
  · intro hw
    obtain ⟨z, hz, hzw⟩ := exists_sqrt_pos_re w hw
    exact ⟨z, hz, hzw⟩

lemma sq_image_neg : (fun w : ℂ => w ^ 2) '' {z : ℂ | z.re < 0} = slitPlane := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact sq_image_neg_subset z hz
  · intro hw
    obtain ⟨z, hz, hzw⟩ := exists_sqrt_pos_re w hw
    refine ⟨-z, ?_, ?_⟩
    · show (-z).re < 0
      simp only [Complex.neg_re]
      linarith
    · show (-z) ^ 2 = w
      rw [neg_sq]
      exact hzw

/-- Change of variables for `w ↦ w²` on a set where it is injective. -/
lemma sq_change (S : Set ℂ) (hS : MeasurableSet S) (hinj : InjOn (fun w : ℂ => w ^ 2) S)
    (g : ℂ → ℂ) :
    ∫ w in (fun w : ℂ => w ^ 2) '' S, g w =
      ∫ z in S, ((4 * ‖z‖ ^ 2 : ℝ) : ℂ) * g (z ^ 2) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z _ => (hasFDerivAt_sq z).hasFDerivWithinAt) hinj g]
  refine setIntegral_congr_fun hS (fun z _ => ?_)
  rw [det_mul_two, abs_of_nonneg (by positivity), Complex.real_smul]

lemma half_change (S : Set ℂ) (hS : MeasurableSet S) (hinj : InjOn (fun w : ℂ => w ^ 2) S)
    (hS0 : ∀ z ∈ S, z ≠ 0) (G : ℂ → ℂ) :
    ∫ z in S, G (z ^ 2) =
      ∫ w in (fun w : ℂ => w ^ 2) '' S, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * G w := by
  rw [sq_change S hS hinj (fun w => ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * G w)]
  refine setIntegral_congr_fun hS (fun z hz => ?_)
  have hz0 : z ≠ 0 := hS0 z hz
  have hpos : (0 : ℝ) < 4 * ‖z‖ ^ 2 := by
    have := norm_pos_iff.mpr hz0
    positivity
  have hn : ((4 * ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [norm_pow, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

lemma null_of_ker (f : ℂ →ₗ[ℝ] ℝ) (hf : f ≠ 0) (A : Set ℂ) (hA : ∀ z ∈ A, f z = 0) :
    volume A = 0 := by
  have hK : LinearMap.ker f ≠ ⊤ := fun h => hf (LinearMap.ker_eq_top.mp h)
  have h0 := Measure.addHaar_submodule volume (LinearMap.ker f) hK
  exact measure_mono_null (fun z hz => LinearMap.mem_ker.mpr (hA z hz)) h0

lemma imLm_ne_zero : (Complex.imLm : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h I
  simp at this

lemma reLm_ne_zero : (Complex.reLm : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h 1
  simp at this

lemma compl_slit_null : volume (slitPlaneᶜ : Set ℂ) = 0 :=
  null_of_ker Complex.imLm imLm_ne_zero _ (fun w hw => by
    rw [Set.mem_compl_iff, Complex.mem_slitPlane_iff, not_or, not_not] at hw
    show w.im = 0
    exact hw.2)

lemma integral_slit (g : ℂ → ℂ) : ∫ w in slitPlane, g w = ∫ w, g w := by
  have h : slitPlane =ᵐ[volume] (univ : Set ℂ) := ae_eq_univ.mpr compl_slit_null
  rw [setIntegral_congr_set h, setIntegral_univ]

lemma integral_split_re (F : ℂ → ℂ) (hF : Integrable F) :
    ∫ z, F z = (∫ z in {z : ℂ | 0 < z.re}, F z) + ∫ z in {z : ℂ | z.re < 0}, F z := by
  have hmeas : MeasurableSet {z : ℂ | 0 < z.re} :=
    measurableSet_lt measurable_const Complex.measurable_re
  rw [← integral_add_compl hmeas hF]
  congr 1
  apply setIntegral_congr_set
  rw [ae_eq_set]
  constructor
  · apply null_of_ker Complex.reLm reLm_ne_zero
    intro z hz
    simp only [mem_sdiff, mem_compl_iff, mem_ofPred_eq, not_lt] at hz
    show z.re = 0
    linarith [hz.1, hz.2]
  · apply null_of_ker Complex.reLm reLm_ne_zero
    intro z hz
    simp only [mem_sdiff, mem_compl_iff, mem_ofPred_eq, not_lt] at hz
    exfalso
    linarith [hz.1, hz.2]



/-- `x^{1/2} * conj x^{1/2} = |x|` for `x` with positive real part. -/
lemma cpow_half_mul_conj (x : ℂ) (hx : 0 < x.re) :
    x ^ (1 / 2 : ℂ) * (conj x) ^ (1 / 2 : ℂ) = ((‖x‖ : ℝ) : ℂ) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  have hcx : conj x ≠ 0 := by simpa using hx0
  have harg : x.arg ≠ Real.pi := slitPlane_arg_ne_pi (by
    rw [Complex.mem_slitPlane_iff]
    left
    exact hx)
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hcx, ← Complex.exp_add,
    Complex.log_conj x harg]
  have hadd := Complex.add_conj (Complex.log x)
  have h2 : ((2 * (Complex.log x).re : ℝ) : ℂ) = 2 * ((Real.log ‖x‖ : ℝ) : ℂ) := by
    rw [Complex.log_re]
    push_cast
    ring
  have hsum : Complex.log x * (1 / 2 : ℂ) + conj (Complex.log x) * (1 / 2 : ℂ)
      = ((Real.log ‖x‖ : ℝ) : ℂ) := by
    linear_combination (1 / 2 : ℂ) * hadd + (1 / 2 : ℂ) * h2
  rw [hsum, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hx0)]

lemma norm_sq_b (σ c : ℝ) :
    ‖((σ : ℂ) - I * c / 2)‖ = Real.sqrt (σ ^ 2 + c ^ 2 / 4) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_re,
    Complex.div_im]
  norm_num
  ring

/-- The value of the complex Gaussian over `ℂ`, after the reduction to `ℝ²`. -/
lemma gauss_phase (σ c : ℝ) (hσ : 0 < σ) :
    ∫ w : ℂ, cexp (-(σ : ℂ) * ((‖w‖ ^ 2 : ℝ) : ℂ) + (I * c / 4) * (w ^ 2 + conj w ^ 2))
      = ((π * (σ ^ 2 + c ^ 2 / 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  set b1 : ℂ := (σ : ℂ) - I * c / 2 with hb1
  set b2 : ℂ := (σ : ℂ) + I * c / 2 with hb2
  have hre1 : b1.re = σ := by rw [hb1]; simp
  have hre2 : b2.re = σ := by rw [hb2]; simp
  have hpos1 : 0 < b1.re := by rw [hre1]; exact hσ
  have hpos2 : 0 < b2.re := by rw [hre2]; exact hσ
  have hb0 : b1 ≠ 0 := fun h => by
    have := hpos1
    rw [h] at this
    simp at this
  have hconj : conj b1 = b2 := by
    rw [hb1, hb2]
    simp only [map_sub, map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  have key : ∀ p : ℝ × ℝ,
      cexp (-(σ : ℂ) * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ)
        + (I * c / 4) * (measurableEquivRealProd.symm p ^ 2
          + conj (measurableEquivRealProd.symm p) ^ 2))
        = cexp (-b1 * (p.1 : ℂ) ^ 2) * cexp (-b2 * (p.2 : ℂ) ^ 2) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    obtain ⟨x, y⟩ := p
    have hs : measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := by
      simp
    rw [hs]
    have h1 : ((‖(⟨x, y⟩ : ℂ)‖ ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      push_cast
      ring
    have h2 : (⟨x, y⟩ : ℂ) ^ 2 + conj (⟨x, y⟩ : ℂ) ^ 2 = ((2 * (x ^ 2 - y ^ 2) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [pow_two] <;> ring
    rw [h1, h2, hb1, hb2]
    push_cast
    ring
  have hsplit : ∫ w : ℂ, cexp (-(σ : ℂ) * ((‖w‖ ^ 2 : ℝ) : ℂ) + (I * c / 4) * (w ^ 2 + conj w ^ 2))
      = ∫ p : ℝ × ℝ, cexp (-(σ : ℂ) * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ)
        + (I * c / 4) * (measurableEquivRealProd.symm p ^ 2
          + conj (measurableEquivRealProd.symm p) ^ 2)) :=
    ((Complex.volume_preserving_equiv_real_prod.symm).integral_comp'
      (fun w : ℂ => cexp (-(σ : ℂ) * ((‖w‖ ^ 2 : ℝ) : ℂ) + (I * c / 4) * (w ^ 2 + conj w ^ 2)))).symm
  have hval : ∫ p : ℝ × ℝ, cexp (-(σ : ℂ) * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ)
        + (I * c / 4) * (measurableEquivRealProd.symm p ^ 2
          + conj (measurableEquivRealProd.symm p) ^ 2))
      = (π / b1) ^ (1 / 2 : ℂ) * (π / b2) ^ (1 / 2 : ℂ) := by
    calc ∫ p : ℝ × ℝ, cexp (-(σ : ℂ) * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ)
            + (I * c / 4) * (measurableEquivRealProd.symm p ^ 2
              + conj (measurableEquivRealProd.symm p) ^ 2))
        = ∫ p : ℝ × ℝ, cexp (-b1 * (p.1 : ℂ) ^ 2) * cexp (-b2 * (p.2 : ℂ) ^ 2) :=
          integral_congr_ae (Filter.Eventually.of_forall key)
      _ = (∫ x : ℝ, cexp (-b1 * (x : ℂ) ^ 2)) * (∫ y : ℝ, cexp (-b2 * (y : ℂ) ^ 2)) := by
          rw [Measure.volume_eq_prod ℝ ℝ]
          exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := ℂ)
            (fun x : ℝ => cexp (-b1 * (x : ℂ) ^ 2)) (fun y : ℝ => cexp (-b2 * (y : ℂ) ^ 2))
      _ = (π / b1) ^ (1 / 2 : ℂ) * (π / b2) ^ (1 / 2 : ℂ) := by
          rw [integral_gaussian_complex hpos1, integral_gaussian_complex hpos2]
  rw [hsplit, hval]
  have hx : 0 < ((π : ℂ) / b1).re := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_div]
    exact div_pos (mul_pos Real.pi_pos hpos1) (Complex.normSq_pos.mpr hb0)
  have hxc : conj ((π : ℂ) / b1) = (π : ℂ) / b2 := by
    rw [map_div₀, hconj, Complex.conj_ofReal]
  have hn : ‖b1‖ = Real.sqrt (σ ^ 2 + c ^ 2 / 4) := by
    rw [hb1]
    exact norm_sq_b σ c
  rw [← hxc, cpow_half_mul_conj _ hx]
  congr 1
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, hn, Real.sqrt_eq_rpow,
    Real.rpow_neg (by positivity), div_eq_mul_inv]



lemma phase_re (lam : ℝ) (u : ℂ) : ((I * lam / 4) * (u + conj u)).re = 0 := by
  have h := Complex.add_conj u
  rw [h, Complex.mul_re]
  simp

lemma norm_phase (lam : ℝ) (u : ℂ) : ‖cexp ((I * lam / 4) * (u + conj u))‖ = 1 := by
  rw [Complex.norm_exp, phase_re, Real.exp_zero]

/-- The real Gaussian over `ℂ`. -/
lemma gauss_real (σ : ℝ) (hσ : 0 < σ) :
    ∫ w : ℂ, Real.exp (-σ * ‖w‖ ^ 2) = π / σ := by
  have hs : ∀ x y : ℝ, Real.exp (-σ * ‖(measurableEquivRealProd.symm (x, y))‖ ^ 2)
      = Real.exp (-σ * x ^ 2) * Real.exp (-σ * y ^ 2) := by
    intro x y
    have hsym : measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := by simp
    rw [hsym, ← Real.exp_add, Complex.norm_def, Complex.normSq_mk]
    congr 1
    rw [Real.sq_sqrt (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y))]
    ring
  have hsplit : ∫ w : ℂ, Real.exp (-σ * ‖w‖ ^ 2)
      = ∫ p : ℝ × ℝ, Real.exp (-σ * ‖(measurableEquivRealProd.symm p)‖ ^ 2) := by
    exact ((Complex.volume_preserving_equiv_real_prod.symm).integral_comp'
      (fun w : ℂ => Real.exp (-σ * ‖w‖ ^ 2))).symm
  rw [hsplit]
  calc ∫ p : ℝ × ℝ, Real.exp (-σ * ‖(measurableEquivRealProd.symm p)‖ ^ 2)
      = ∫ p : ℝ × ℝ, (fun x : ℝ => Real.exp (-σ * x ^ 2)) p.1 *
          (fun y : ℝ => Real.exp (-σ * y ^ 2)) p.2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun p => hs p.1 p.2)
    _ = (∫ x : ℝ, Real.exp (-σ * x ^ 2)) * (∫ y : ℝ, Real.exp (-σ * y ^ 2)) := by
        rw [Measure.volume_eq_prod ℝ ℝ]
        exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (fun x : ℝ => Real.exp (-σ * x ^ 2)) (fun y : ℝ => Real.exp (-σ * y ^ 2))
    _ = π / σ := by
        rw [integral_gaussian σ, ← sq, Real.sq_sqrt (by positivity)]

/-- The Fubini integrand: the subordinated weight times the phase. -/
noncomputable def PhiF (a lam : ℝ) (w : ℂ) (σ : ℝ) : ℂ :=
  ((σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(‖w‖ ^ 2 * σ) - (a ^ 2 / 4) / σ) : ℝ) : ℂ)
    * cexp ((I * lam / 4) * (w ^ 2 + conj w ^ 2))

/-- The integrand of the Gaussian over `ℂ` in `gauss_phase`. -/
noncomputable def Psi (lam σ : ℝ) (w : ℂ) : ℂ :=
  cexp (-(σ : ℂ) * ((‖w‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (w ^ 2 + conj w ^ 2))

/-- The integrand `G(w)` with `z⁴ + z̄⁴` written through `w = z²`. -/
noncomputable def GwSrc (a lam : ℝ) (w : ℂ) : ℂ :=
  cexp (-(a : ℂ) * ((‖w‖ : ℝ) : ℂ) + (I * lam / 4) * (w ^ 2 + conj w ^ 2))

lemma PhiF_eq_Psi (a lam : ℝ) (w : ℂ) (σ : ℝ) :
    PhiF a lam w σ = ((σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) : ℝ) : ℂ)
      * Psi lam σ w := by
  have hB : ((Real.exp (-(‖w‖ ^ 2 * σ) - (a ^ 2 / 4) / σ) : ℝ) : ℂ)
      = ((Real.exp (-((a ^ 2 / 4) / σ)) : ℝ) : ℂ) * cexp (-(σ : ℂ) * ((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold PhiF Psi
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hB, Complex.exp_add]
  ring



lemma norm_phase_w (lam : ℝ) (w : ℂ) : ‖cexp ((I * lam / 4) * (w ^ 2 + conj w ^ 2))‖ = 1 := by
  have h := norm_phase lam (w ^ 2)
  rw [map_pow] at h
  exact h

lemma norm_PhiF (a lam σ : ℝ) (hσ : 0 < σ) (w : ℂ) :
    ‖PhiF a lam w σ‖ = σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) * Real.exp (-σ * ‖w‖ ^ 2) := by
  unfold PhiF
  rw [norm_mul, norm_phase_w, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  rw [show -(‖w‖ ^ 2 * σ) - (a ^ 2 / 4) / σ = -((a ^ 2 / 4) / σ) + -σ * ‖w‖ ^ 2 by ring,
    Real.exp_add]
  ring

lemma integrable_PhiF_slice (a lam σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun w : ℂ => PhiF a lam w σ) := by
  refine Integrable.mono' ((integrable_gauss (2 * σ) (by linarith)).const_mul
    (σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold PhiF
    fun_prop
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_PhiF a lam σ hσ w]
    have e : -(2 * σ / 2) * ‖w‖ ^ 2 = -σ * ‖w‖ ^ 2 := by ring
    simp only [e]
    exact le_of_eq (by ring)

lemma integral_norm_PhiF (a lam σ : ℝ) (hσ : 0 < σ) :
    ∫ w : ℂ, ‖PhiF a lam w σ‖ = σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) * (π / σ) := by
  calc ∫ w : ℂ, ‖PhiF a lam w σ‖
      = ∫ w : ℂ, σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) * Real.exp (-σ * ‖w‖ ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => norm_PhiF a lam σ hσ w)
    _ = σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) * (π / σ) := by
        rw [integral_const_mul, gauss_real σ hσ]

/-- The σ-integrability of the Fubini majorant, through `σ ↦ 1/σ`. -/
lemma integrable_majorant (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) * (π / σ))
      (Ioi 0) := by
  have hq : 0 < a ^ 2 / 4 := div_pos (pow_pos ha 2) (by norm_num)
  have hg : IntegrableOn (fun y : ℝ => π * (y ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 / 4) * y ^ (1 : ℝ))))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2 : ℝ)) (p := 1) (b := a ^ 2 / 4)
      (by norm_num) one_pos hq).const_mul π
  have key := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun t : ℝ => 1 / t)
    (f' := fun x => -(1 / x ^ 2)) measurableSet_Ioi
    (fun x hx => (subord_hasDeriv_inv 1 (mem_Ioi.mp hx)).hasDerivWithinAt)
    (subord_injOn_inv 1 one_pos)
    (fun y : ℝ => π * (y ^ (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2 / 4) * y ^ (1 : ℝ))))
  rw [subord_image_inv 1 one_pos] at key
  refine (key.mp hg).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := hx
  simp only [smul_eq_mul]
  have hinv : (1 / x) ^ (-(1 / 2 : ℝ)) = (x ^ (-(1 / 2 : ℝ)))⁻¹ := by
    rw [one_div, Real.inv_rpow hx0.le]
  have hyy : x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_add hx0, show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hyi : (x ^ (-(1 / 2 : ℝ)))⁻¹ = x ^ (-(1 / 2 : ℝ)) * x :=
    inv_eq_of_mul_eq_one_right (by
      linear_combination x * hyy + mul_inv_cancel₀ hx0.ne')
  have he : -(a ^ 2 / 4) * (1 / x) ^ (1 : ℝ) = -(a ^ 2 / 4 / x) := by
    rw [Real.rpow_one]
    ring
  rw [abs_neg, abs_of_pos (by positivity), he, hinv, hyi]
  field_simp



lemma PhiF_meas (a lam : ℝ) : Measurable (fun p : ℂ × ℝ => PhiF a lam p.1 p.2) := by
  unfold PhiF
  fun_prop

lemma fubini_PhiF (a lam : ℝ) (ha : 0 < a) :
    ∫ w : ℂ, ∫ σ in Ioi (0 : ℝ), PhiF a lam w σ = ∫ σ in Ioi (0 : ℝ), ∫ w : ℂ, PhiF a lam w σ := by
  refine integral_integral_swap ?_
  refine (integrable_prod_iff' (PhiF_meas a lam).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact integrable_PhiF_slice a lam σ hσ
  · refine (integrable_majorant a ha).congr_fun (fun σ hσ => ?_) measurableSet_Ioi
    exact (integral_norm_PhiF a lam σ hσ).symm

lemma Gw_eq (a lam : ℝ) (w : ℂ) :
    GwSrc a lam w = ((Real.exp (-(a * ‖w‖)) : ℝ) : ℂ) * cexp ((I * lam / 4) * (w ^ 2 + conj w ^ 2)) := by
  unfold GwSrc
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma inner_sigma (a lam : ℝ) (ha : 0 < a) (w : ℂ) (hw : w ≠ 0) :
    ∫ σ in Ioi (0 : ℝ), PhiF a lam w σ
      = (4 * ((Real.sqrt π : ℝ) : ℂ)) * (((4 * ‖w‖ : ℝ) : ℂ))⁻¹ * GwSrc a lam w := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hp : 0 < ‖w‖ ^ 2 := by positivity
  have hq : 0 < a ^ 2 / 4 := by positivity
  have hsub := Painleve.subordination (‖w‖ ^ 2) (a ^ 2 / 4) hp hq
  have hval : Real.sqrt (π / ‖w‖ ^ 2) * Real.exp (-2 * Real.sqrt (‖w‖ ^ 2 * (a ^ 2 / 4)))
      = Real.sqrt π / ‖w‖ * Real.exp (-(a * ‖w‖)) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq (norm_nonneg w)]
    have e : ‖w‖ ^ 2 * (a ^ 2 / 4) = (a * ‖w‖ / 2) ^ 2 := by ring
    rw [e, Real.sqrt_sq (div_nonneg (mul_nonneg ha.le (norm_nonneg w)) (by norm_num))]
    congr 2
    ring
  have hwc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwn.ne'
  calc ∫ σ in Ioi (0 : ℝ), PhiF a lam w σ
      = ∫ σ in Ioi (0 : ℝ), ((σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(‖w‖ ^ 2 * σ) - (a ^ 2 / 4) / σ) : ℝ) : ℂ)
          * cexp ((I * lam / 4) * (w ^ 2 + conj w ^ 2)) := rfl
    _ = ((∫ σ in Ioi (0 : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-(‖w‖ ^ 2 * σ) - (a ^ 2 / 4) / σ) : ℝ) : ℂ)
          * cexp ((I * lam / 4) * (w ^ 2 + conj w ^ 2)) := by
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ((Real.sqrt π / ‖w‖ * Real.exp (-(a * ‖w‖)) : ℝ) : ℂ)
          * cexp ((I * lam / 4) * (w ^ 2 + conj w ^ 2)) := by
        rw [hsub, hval]
    _ = (4 * ((Real.sqrt π : ℝ) : ℂ)) * (((4 * ‖w‖ : ℝ) : ℂ))⁻¹ * GwSrc a lam w := by
        rw [Gw_eq]
        push_cast
        field_simp

lemma inner_w (a lam σ : ℝ) (hσ : 0 < σ) :
    ∫ w : ℂ, PhiF a lam w σ
      = ((σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) : ℝ) : ℂ)
        * ((π * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun w => PhiF_eq_Psi a lam w σ),
    integral_const_mul]
  congr 1
  exact gauss_phase σ lam hσ



lemma rpow_neg_half (x : ℝ) (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hx]

lemma subst_real (a lam : ℝ) (ha : 0 < a) :
    ∫ σ in Ioi (0 : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ))
        * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ))
      = Real.sqrt 2 * ∫ s in Ioi (0 : ℝ),
          Real.exp (-(a ^ 2 / 2) * s) * s ^ (-(1 / 2 : ℝ)) * (1 + lam ^ 2 * s ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have himg := integral_image_eq_integral_abs_deriv_smul (f := fun t : ℝ => (1 / 2 : ℝ) / t)
    (f' := fun x => -((1 / 2 : ℝ) / x ^ 2)) measurableSet_Ioi
    (fun x hx => (subord_hasDeriv_inv (1 / 2) (mem_Ioi.mp hx)).hasDerivWithinAt)
    (subord_injOn_inv (1 / 2) (by norm_num))
    (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ)) * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ)))
  rw [subord_image_inv (1 / 2) (by norm_num)] at himg
  rw [himg, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs0 : 0 < s := hs
  simp only [smul_eq_mul]
  have hu0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hu2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hr0 : 0 < Real.sqrt 2 := by positivity
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hv0 : 0 < Real.sqrt (1 + lam ^ 2 * s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hv2 : Real.sqrt (1 + lam ^ 2 * s ^ 2) ^ 2 = 1 + lam ^ 2 * s ^ 2 := Real.sq_sqrt (by positivity)
  have hσ : (1 / 2 : ℝ) / s = (1 / (Real.sqrt 2 * Real.sqrt s)) ^ 2 := by
    rw [div_pow, mul_pow, hr2, hu2]
    field_simp
  have hσ2 : ((1 / 2 : ℝ) / s) ^ 2 + lam ^ 2 / 4
      = (Real.sqrt (1 + lam ^ 2 * s ^ 2) / (2 * s)) ^ 2 := by
    rw [div_pow (Real.sqrt (1 + lam ^ 2 * s ^ 2)), hv2]
    field_simp
    ring
  have e1 : Real.sqrt ((1 / 2 : ℝ) / s) = 1 / (Real.sqrt 2 * Real.sqrt s) := by
    rw [hσ, Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt (((1 / 2 : ℝ) / s) ^ 2 + lam ^ 2 / 4)
      = Real.sqrt (1 + lam ^ 2 * s ^ 2) / (2 * s) := by
    rw [hσ2, Real.sqrt_sq (by positivity)]
  have e3 : -((a ^ 2 / 4) / ((1 / 2 : ℝ) / s)) = -(a ^ 2 / 2) * s := by
    field_simp
    ring
  rw [rpow_neg_half _ (by positivity), rpow_neg_half _ (by positivity), e1, e2, e3,
    rpow_neg_half s hs0.le, rpow_neg_half _ (by positivity), abs_neg, abs_of_pos (by positivity)]
  generalize hr : Real.sqrt 2 = r at hr0 hr2 ⊢
  generalize hv : Real.sqrt (1 + lam ^ 2 * s ^ 2) = v at hv0 hv2 ⊢
  generalize hu : Real.sqrt s = u at hu0 hu2 ⊢
  generalize hE : Real.exp (-(a ^ 2 / 2) * s) = E
  subst hu2
  have hu' : u ≠ 0 := hu0.ne'
  have hv' : v ≠ 0 := hv0.ne'
  have hr' : r ≠ 0 := hr0.ne'
  field_simp



/-- **Lemma 4.1**: the planar integral of the quartic density. -/
theorem planar_source (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ∫ z : ℂ, Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4)) =
      ((Real.sqrt (Real.pi / 2) * ∫ s in Set.Ioi (0 : ℝ),
        Real.exp (-(a ^ 2 / 2) * s) * s ^ (-(1 / 2) : ℝ) * (1 + lam ^ 2 * s ^ 2) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have hcongr : ∀ z : ℂ, Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))
      = GwSrc a lam (z ^ 2) := by
    intro z
    unfold GwSrc
    congr 1
    rw [norm_pow]
    simp only [map_pow]
    ring
  have hint : Integrable (fun z : ℂ =>
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))) := by
    refine Integrable.mono' (integrable_gauss (2 * a) (by linarith)) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · refine Filter.Eventually.of_forall fun z => ?_
      have hph : ((I * lam / 4) * (z ^ 4 + conj z ^ 4)).re = 0 := by
        rw [show conj z ^ 4 = conj (z ^ 4) from (map_pow _ _ _).symm]
        exact phase_re lam (z ^ 4)
      have hre : (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)).re = -(a * ‖z‖ ^ 2) := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      rw [Complex.norm_exp, Complex.add_re, hph, add_zero, hre]
      apply le_of_eq
      congr 1
      ring
  have hmeasP : MeasurableSet {z : ℂ | 0 < z.re} :=
    measurableSet_lt measurable_const Complex.measurable_re
  have hmeasN : MeasurableSet {z : ℂ | z.re < 0} :=
    measurableSet_lt Complex.measurable_re measurable_const
  have hpos : ∫ z in {z : ℂ | 0 < z.re},
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))
      = ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w := by
    calc ∫ z in {z : ℂ | 0 < z.re},
          Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))
        = ∫ z in {z : ℂ | 0 < z.re}, GwSrc a lam (z ^ 2) :=
          setIntegral_congr_fun hmeasP (fun z _ => hcongr z)
      _ = ∫ w in (fun w : ℂ => w ^ 2) '' {z : ℂ | 0 < z.re}, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w :=
          half_change _ hmeasP sq_injOn_pos (fun z hz h => by
            have hz' : (0 : ℝ) < z.re := hz
            rw [h] at hz'
            simp at hz') (GwSrc a lam)
      _ = ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w := by
          rw [sq_image_pos, integral_slit]
  have hneg : ∫ z in {z : ℂ | z.re < 0},
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))
      = ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w := by
    calc ∫ z in {z : ℂ | z.re < 0},
          Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))
        = ∫ z in {z : ℂ | z.re < 0}, GwSrc a lam (z ^ 2) :=
          setIntegral_congr_fun hmeasN (fun z _ => hcongr z)
      _ = ∫ w in (fun w : ℂ => w ^ 2) '' {z : ℂ | z.re < 0}, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w :=
          half_change _ hmeasN sq_injOn_neg (fun z hz h => by
            have hz' : z.re < 0 := hz
            rw [h] at hz'
            simp at hz') (GwSrc a lam)
      _ = ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w := by
          rw [sq_image_neg, integral_slit]
  have hsplit_eq : ∫ z : ℂ,
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I * lam / 4) * (z ^ 4 + conj z ^ 4))
      = 2 * ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w := by
    rw [integral_split_re _ hint, hpos, hneg]
    ring
  -- Fubini and subordination for the weight `((4‖w‖)⁻¹ G(w))`.
  have hae : ∀ᵐ w : ℂ ∂volume, w ≠ 0 :=
    Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ)))
      (fun w hw => Set.mem_compl_singleton_iff.mp hw)
  have hA : ∫ w : ℂ, ∫ σ in Ioi (0 : ℝ), PhiF a lam w σ
      = (4 * ((Real.sqrt π : ℝ) : ℂ)) * ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w := by
    rw [← integral_const_mul]
    exact integral_congr_ae (hae.mono fun w hw =>
      (inner_sigma a lam ha w hw).trans (mul_assoc _ _ _))
  have hB : ∫ σ in Ioi (0 : ℝ), ∫ w : ℂ, PhiF a lam w σ
      = ((π * ∫ σ in Ioi (0 : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ))
          * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    calc ∫ σ in Ioi (0 : ℝ), ∫ w : ℂ, PhiF a lam w σ
        = ∫ σ in Ioi (0 : ℝ), ((π * (σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ))
            * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) :=
          setIntegral_congr_fun measurableSet_Ioi (fun σ hσ => by
            have hσ' : 0 < σ := hσ
            rw [inner_w a lam σ hσ', ← Complex.ofReal_mul]
            congr 1
            ring)
      _ = ((∫ σ in Ioi (0 : ℝ), π * (σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ))
            * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := integral_complex_ofReal
      _ = ((π * ∫ σ in Ioi (0 : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ))
            * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
          rw [integral_const_mul]
  have hkey : (4 * ((Real.sqrt π : ℝ) : ℂ)) * ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w
      = ((π * ∫ σ in Ioi (0 : ℝ), σ ^ (-(1 / 2 : ℝ)) * Real.exp (-((a ^ 2 / 4) / σ))
          * (σ ^ 2 + lam ^ 2 / 4) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← hA, fubini_PhiF a lam ha, hB]
  have hJ := subst_real a lam ha
  rw [hJ] at hkey
  rw [hsplit_eq]
  set I := ∫ w : ℂ, ((4 * ‖w‖ : ℝ) : ℂ)⁻¹ * GwSrc a lam w with hI
  set R := ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-(a ^ 2 / 2) * s) * s ^ (-(1 / 2) : ℝ) * (1 + lam ^ 2 * s ^ 2) ^ (-(1 / 2) : ℝ) with hR
  have hsq : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = (π : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hsqrt2 : Real.sqrt (π / 2) = Real.sqrt π * Real.sqrt 2 / 2 := by
    have h : π / 2 = (Real.sqrt π * Real.sqrt 2 / 2) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [h, Real.sqrt_sq (by positivity)]
  have hkey2 : 4 * (Real.sqrt π : ℂ) * I = (π : ℂ) * ((Real.sqrt 2 : ℂ) * (R : ℂ)) := by
    push_cast at hkey
    linear_combination hkey
  apply mul_left_cancel₀ (show (2 * (Real.sqrt π : ℂ)) ≠ 0 from
    mul_ne_zero two_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'))
  rw [hsqrt2]
  push_cast
  linear_combination hkey2 - ((Real.sqrt 2 : ℂ) * (R : ℂ)) * hsq

end Painleve
