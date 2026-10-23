import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Positivity of symmetric integrals over `ℝ^k`

If `F` is integrable on `ℝ^k`, invariant under permutations of the coordinates,
and `s F(w) > 0` at every strictly increasing `w`, then `s ∫ F > 0`. Points with
two equal coordinates form a null set, and every other point is a permutation
of an increasing one (`lem:hankel-signs`: "together with the symmetry of the
integrand", "the integrand has sign `(-1)^{k(k-1)/2}` and does not vanish").
-/

open MeasureTheory Set Filter

namespace Painleve

lemma volume_eq_coords_null {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    volume {w : Fin k → ℝ | w i = w j} = 0 := by
  let L : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j
  have hset : {w : Fin k → ℝ | w i = w j} = (LinearMap.ker L : Set (Fin k → ℝ)) := by
    ext w; simp [L, sub_eq_zero]
  rw [hset]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have hmem : (Pi.single i 1 : Fin k → ℝ) ∈ LinearMap.ker L := by rw [htop]; trivial
  simp [L, Pi.single_apply, hij, hij.symm] at hmem

lemma ae_injective (k : ℕ) : ∀ᵐ w : Fin k → ℝ, Function.Injective w := by
  have hnull : volume {w : Fin k → ℝ | ¬ Function.Injective w} = 0 := by
    have hsub : {w : Fin k → ℝ | ¬ Function.Injective w}
        ⊆ ⋃ i : Fin k, ⋃ j : Fin k, ⋃ (_ : i ≠ j), {w : Fin k → ℝ | w i = w j} := by
      intro w hw
      simp only [Function.Injective, not_forall, mem_ofPred_eq] at hw
      obtain ⟨i, j, hij, hne⟩ := hw
      simp only [mem_iUnion]
      exact ⟨i, j, hne, hij⟩
    refine measure_mono_null hsub ?_
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun h => ?_
    exact volume_eq_coords_null h
  rw [ae_iff]
  simpa using hnull

/-- **Symmetrization**: positivity at increasing points gives a positive integral. -/
theorem integral_pos_of_sym {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : Integrable F) (s : ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) (w : Fin k → ℝ), F (w ∘ σ) = F w)
    (hpos : ∀ w : Fin k → ℝ, StrictMono w → 0 < s * F w) :
    0 < s * ∫ w, F w := by
  have hae : ∀ᵐ w : Fin k → ℝ, 0 < s * F w := by
    filter_upwards [ae_injective k] with w hw
    have hmono : StrictMono (w ∘ Tuple.sort w) :=
      (Tuple.monotone_sort w).strictMono_of_injective (hw.comp (Tuple.sort w).injective)
    rw [← hsym (Tuple.sort w) w]
    exact hpos _ hmono
  rw [← integral_const_mul]
  have hint : Integrable (fun w => s * F w) := hF.const_mul s
  rw [integral_pos_iff_support_of_nonneg_ae (hae.mono fun w hw => hw.le) hint]
  by_contra h
  push Not at h
  have hzero : volume (Function.support fun w => s * F w) = 0 := le_antisymm h (zero_le)
  have hnot : ∀ᵐ w : Fin k → ℝ, w ∉ Function.support fun w => s * F w :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have hfalse : ∀ᵐ w : Fin k → ℝ, False := by
    filter_upwards [hae, hnot] with w h1 h2
    exact h2 (Function.mem_support.mpr h1.ne')
  haveI : (ae (volume : Measure (Fin k → ℝ))).NeBot := ae_neBot.mpr (NeZero.ne _)
  exact hfalse.exists.elim fun _ h => h

end Painleve
