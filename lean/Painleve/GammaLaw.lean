import Painleve.LogGamma
import Painleve.StatementD

/-!
# Gauss's multiplication formula in law

For `U ~ Gamma(r+1)` the law of `d log U` equals that of
`d log d + log G + ∑_{j ∈ J_r} log G_j`, where `G ~ Exp(1)` and the `G_j` are
independent Gamma variables with shapes `β_{r,j} = (r+1+j)/d`,
`J_r = {0,…,d-1} \ {d-1-r}`. Both laws have the same characteristic function by
the complex Gauss multiplication formula (`cGamma_ratio_mult`); the factor with
`j = d-1-r` has shape `1`. This is Steps 2–4 of `prop:gamma`.
-/

open MeasureTheory Set Filter Complex
open scoped MeasureTheory Real

namespace Painleve

/-- The index list `J_r = {0,…,d-1} \ {d-1-r}`, in increasing order. -/
def shapeIdx (d r : ℕ) : List ℕ := (List.range d).filter (fun j => j ≠ d - 1 - r)

/-- The shapes `β_{r,j} = (r+1+j)/d`, `j ∈ J_r`. -/
noncomputable def shapesD (d r : ℕ) : List ℝ := (shapeIdx d r).map (shapeD d r)

lemma shapeD_pos (d r j : ℕ) (hd : 0 < d) : 0 < shapeD d r j := by
  unfold shapeD
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  positivity

lemma shapesD_pos (d r : ℕ) (hd : 0 < d) : ∀ β ∈ shapesD d r, 0 < β := by
  intro β hβ
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hβ
  exact shapeD_pos d r j hd

lemma list_prod_filter_range {M : Type*} [CommMonoid M] (d : ℕ) (p : ℕ → Prop)
    [DecidablePred p] (F : ℕ → M) :
    (((List.range d).filter (fun j => decide (p j))).map F).prod
      = ∏ k ∈ (Finset.range d).filter p, F k := by
  rw [Finset.prod_eq_multiset_prod, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.map_coe, Multiset.prod_coe]

lemma shapeD_omitted (d r : ℕ) (hd : 0 < d) (hr : r < d) : shapeD d r (d - 1 - r) = 1 := by
  unfold shapeD
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  field_simp
  ring

lemma ofReal_natCast_cpow_mul_I (d : ℕ) (hd : 0 < d) (s : ℝ) :
    (d : ℂ) ^ ((s : ℂ) * I) = cexp (((Real.log d * s : ℝ) : ℂ) * I) := by
  have hne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [cpow_def_of_ne_zero hne, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg d)]
  push_cast
  ring_nf

/-- **Gauss's multiplication formula in law.** -/
theorem law_eq (d r : ℕ) (hd : 0 < d) (hr : r < d) :
    (logGammaLaw ((r : ℝ) + 1)).map (fun v => (d : ℝ) * v)
      = (logGammaLaw 1 ∗ prodLaw (shapesD d r)).map (fun y => y + (d : ℝ) * Real.log d) := by
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  haveI := isProbabilityMeasure_logGammaLaw' hr1
  haveI := isProbabilityMeasure_logGammaLaw' (one_pos (α := ℝ))
  haveI := isProbabilityMeasure_prodLaw (shapesD d r) (shapesD_pos d r hd)
  haveI : IsProbabilityMeasure ((logGammaLaw ((r : ℝ) + 1)).map (fun v => (d : ℝ) * v)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure
      ((logGammaLaw 1 ∗ prodLaw (shapesD d r)).map (fun y => y + (d : ℝ) * Real.log d)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_mul, charFun_logGammaLaw hr1,
    charFun_map_add_const, charFun_conv, charFun_logGammaLaw one_pos,
    charFun_prodLaw _ (shapesD_pos d r hd), Real.inner_apply]
  -- the complex Gauss multiplication formula at `x = r+1+idt`, `y = r+1`
  have hx : 0 < (((r : ℝ) + 1 : ℝ) + ((d * t : ℝ) : ℂ) * I : ℂ).re := by simpa using hr1
  have hy : 0 < ((((r : ℝ) + 1 : ℝ)) : ℂ).re := by simpa using hr1
  rw [cGamma_ratio_mult d hd hx hy]
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hshift : ∀ k : ℕ, ((((r : ℝ) + 1 : ℝ) + ((d * t : ℝ) : ℂ) * I : ℂ) + k) / d
      = (shapeD d r k : ℂ) + t * I := by
    intro k; unfold shapeD; push_cast; field_simp; ring
  have hshift0 : ∀ k : ℕ, (((((r : ℝ) + 1 : ℝ)) : ℂ) + k) / d = (shapeD d r k : ℂ) := by
    intro k; unfold shapeD; push_cast; ring
  simp_rw [hshift, hshift0]
  have hpow : (d : ℂ) ^ ((((r : ℝ) + 1 : ℝ) + ((d * t : ℝ) : ℂ) * I : ℂ)
      - ((((r : ℝ) + 1 : ℝ)) : ℂ)) = cexp (((d * Real.log d * t : ℝ) : ℂ) * I) := by
    rw [show (((((r : ℝ) + 1 : ℝ) + ((d * t : ℝ) : ℂ) * I : ℂ) - ((((r : ℝ) + 1 : ℝ)) : ℂ)))
        = ((d * t : ℝ) : ℂ) * I by ring, ofReal_natCast_cpow_mul_I d hd]
    congr 3; ring
  rw [hpow]
  -- split off the factor `k = d-1-r`, whose shape is `1`
  have hmem : d - 1 - r ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.filter_ne', shapeD_omitted d r hd hr]
  rw [shapesD, shapeIdx, List.map_map, list_prod_filter_range]
  simp only [Function.comp_def]
  push_cast
  ring

end Painleve
