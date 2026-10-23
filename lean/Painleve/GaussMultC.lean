import Painleve.GaussMult
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Gauss's multiplication formula on the right half-plane

The real formula `multGamma_eq_Gamma` extends to `Re s > 0` by the identity
theorem: both sides are holomorphic on the connected half-plane and agree on
the positive reals. The ratio form `cGamma_ratio_mult` gives the characteristic
functions in the Gamma representation (`prop:gamma`).
-/

open Complex Filter Topology Set

namespace Painleve

/-- `d^{s-1} ∏_{k<d} Γ((s+k)/d) / ∏_{k<d} Γ((1+k)/d)` for complex `s`. -/
noncomputable def multGammaC (d : ℕ) (s : ℂ) : ℂ :=
  (d : ℂ) ^ (s - 1) * (∏ k ∈ Finset.range d, Complex.Gamma ((s + k) / d)) /
    ∏ k ∈ Finset.range d, Complex.Gamma ((1 + k) / d)

lemma multGammaC_ofReal (d : ℕ) (x : ℝ) : multGammaC d x = (multGamma d x : ℂ) := by
  unfold multGammaC multGamma
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (((d : ℝ) ^ (x - 1) : ℝ) : ℂ) = (d : ℂ) ^ ((x : ℂ) - 1) := by
    rw [ofReal_cpow hd]; push_cast; ring_nf
  have h2 : ∀ k : ℕ, ((Real.Gamma ((x + k) / d) : ℝ) : ℂ) = Complex.Gamma (((x : ℂ) + k) / d) := by
    intro k; rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have h3 : ∀ k : ℕ, ((Real.Gamma ((1 + k) / d) : ℝ) : ℂ) = Complex.Gamma ((1 + k) / d) := by
    intro k; rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  rw [Complex.ofReal_div, Complex.ofReal_mul, h1, Complex.ofReal_prod, Complex.ofReal_prod]
  simp_rw [h2, h3]

lemma gamma_ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s ≠ -m := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma re_shift_pos (d : ℕ) (hd : 0 < d) {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    0 < ((s + k) / d).re := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [show ((s + k) / (d : ℂ)) = (s + k) * ((d : ℝ)⁻¹ : ℝ) by push_cast; ring]
  rw [Complex.re_mul_ofReal]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  simp only [add_re, natCast_re]
  positivity

lemma differentiableOn_multGammaC (d : ℕ) (hd : 0 < d) :
    DifferentiableOn ℂ (multGammaC d) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold multGammaC
  refine DifferentiableAt.div_const (DifferentiableAt.mul ?_ ?_) _
  · exact (differentiableAt_id.sub_const 1).const_cpow (Or.inl hd0)
  · refine DifferentiableAt.fun_finsetProd fun k _ => ?_
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (s + k) / d) s :=
      (differentiableAt_id.add_const _).div_const _
    exact (differentiableAt_Gamma _ (gamma_ne_neg_nat_of_re_pos (re_shift_pos d hd hs k))).comp
      s h1

lemma differentiableOn_Gamma_re_pos :
    DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} :=
  fun s hs => (differentiableAt_Gamma s (gamma_ne_neg_nat_of_re_pos hs)).differentiableWithinAt

/-- Gauss's multiplication formula for `Re s > 0`. -/
theorem cGamma_eq_multGammaC (d : ℕ) (hd : 0 < d) {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s = multGammaC d s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), Complex.Gamma z = multGammaC d z := by
    have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := {(1 : ℝ)}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ), Complex.Gamma (t : ℂ) = multGammaC d (t : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)] with t ht
      rw [Complex.Gamma_ofReal, multGammaC_ofReal, multGamma_eq_Gamma d hd ht]
    exact hT.frequently hev.frequently
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (differentiableOn_Gamma_re_pos.analyticOnNhd hU)
    ((differentiableOn_multGammaC d hd).analyticOnNhd hU) hpre (by simp) hfreq hs

/-- Ratio form for `Re x, Re y > 0`:
`Γ(x)/Γ(y) = d^{x-y} ∏_{k<d} Γ((x+k)/d)/Γ((y+k)/d)`. -/
theorem cGamma_ratio_mult (d : ℕ) (hd : 0 < d) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.Gamma x / Complex.Gamma y
      = (d : ℂ) ^ (x - y) *
          ∏ k ∈ Finset.range d, (Complex.Gamma ((x + k) / d) / Complex.Gamma ((y + k) / d)) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [cGamma_eq_multGammaC d hd hx, cGamma_eq_multGammaC d hd hy]
  unfold multGammaC
  have hC : ∏ k ∈ Finset.range d, Complex.Gamma ((1 + k) / d) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ => Complex.Gamma_ne_zero_of_re_pos ?_
    have := re_shift_pos d hd (s := 1) (by simp) k
    simpa [add_comm] using this
  have hPy : ∏ k ∈ Finset.range d, Complex.Gamma ((y + k) / d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ =>
      Complex.Gamma_ne_zero_of_re_pos (re_shift_pos d hd hy k)
  have hxy : (d : ℂ) ^ (x - 1) = (d : ℂ) ^ (x - y) * (d : ℂ) ^ (y - 1) := by
    rw [← cpow_add _ _ hd0]; congr 1; ring
  have hy0 : (d : ℂ) ^ (y - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hd0)
  rw [Finset.prod_div_distrib, hxy]
  field_simp

end Painleve
