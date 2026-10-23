import Painleve.Andreief
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory
namespace Painleve

open Matrix

/-- Determinant of the matrix `[g(x_j)^p h(x_j)]_{p,j}`. -/
theorem det_evalMatrix_gh {k : ℕ} (g h : ℝ → ℝ) (x : Fin k → ℝ) :
    (evalMatrix (fun (p : Fin k) (s : ℝ) => g s ^ (p : ℕ) * h s) x).det =
      (∏ j, h (x j)) * ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (g (x j) - g (x i)) := by
  have h1 : evalMatrix (fun (p : Fin k) (s : ℝ) => g s ^ (p : ℕ) * h s) x =
      Matrix.of fun p j => h (x j) * (vandermonde (fun j => g (x j)))ᵀ p j := by
    ext p j
    simp [evalMatrix, vandermonde_apply, mul_comm]
  rw [h1, det_mul_row, det_transpose, det_vandermonde]

/-- Each pair factor is nonnegative on the positive half-line. -/
theorem pair_nonneg_of_strictMonoOn (ψ : ℝ → ℝ) (hψ : StrictMonoOn ψ (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (ψ a - ψ b) := by
  rcases lt_trichotomy a b with h | h | h
  · have h1 : ψ a < ψ b := hψ (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · subst h
    simp
  · have h1 : ψ b < ψ a := hψ (Set.mem_Ioi.mpr hb) (Set.mem_Ioi.mpr ha) h
    exact mul_nonneg (by linarith) (by linarith)

/-- Pointwise formula for the Andréief integrand. -/
theorem integrand_eq {k : ℕ} (w ψ : ℝ → ℝ) (x : Fin k → ℝ) :
    (evalMatrix (fun (p : Fin k) (s : ℝ) => s ^ (p : ℕ) * w s) x).det *
        (evalMatrix (fun (q : Fin k) (s : ℝ) => ψ s ^ (q : ℕ)) x).det =
      (∏ j, w (x j)) *
        ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, ((x j - x i) * (ψ (x j) - ψ (x i))) := by
  have e1 := det_evalMatrix_gh (fun s => s) w x
  have e2 := det_evalMatrix_gh ψ (fun _ => (1 : ℝ)) x
  simp only [Finset.prod_const_one, mul_one] at e2
  rw [e1, e2]
  simp only [Finset.prod_mul_distrib]
  ring

set_option maxHeartbeats 400000 in
/-- **Positivity of the bimoment determinant.** -/
theorem det_bimoment_pos {k : ℕ} (w ψ : ℝ → ℝ) (hw : ∀ s, 0 < s → 0 < w s)
    (hψ : StrictMonoOn ψ (Set.Ioi 0))
    (hint : ∀ p q : Fin k, Integrable (fun s => (s ^ (p : ℕ) * w s) * ψ s ^ (q : ℕ))
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    0 < (Matrix.of fun p q : Fin k =>
      ∫ s in Set.Ioi (0 : ℝ), (s ^ (p : ℕ) * w s) * ψ s ^ (q : ℕ)).det := by
  set μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ
  have hkey := andreief μ (fun (p : Fin k) (s : ℝ) => s ^ (p : ℕ) * w s)
    (fun (q : Fin k) (s : ℝ) => ψ s ^ (q : ℕ)) hint
  have hfi := integrable_andreief μ (fun (p : Fin k) (s : ℝ) => s ^ (p : ℕ) * w s)
    (fun (q : Fin k) (s : ℝ) => ψ s ^ (q : ℕ)) hint
  -- almost every point has all coordinates in (0, ∞)
  have hall : ∀ᵐ x ∂(Measure.pi fun _ : Fin k => μ), ∀ j, x j ∈ Set.Ioi (0 : ℝ) := by
    refine ae_all_iff.mpr fun j => ?_
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin k => μ) j).ae
      (ae_restrict_mem measurableSet_Ioi)
  -- the integrand is a.e. nonnegative
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin k => μ]
      (fun x : Fin k → ℝ => (evalMatrix (fun (p : Fin k) (s : ℝ) => s ^ (p : ℕ) * w s) x).det *
        (evalMatrix (fun (q : Fin k) (s : ℝ) => ψ s ^ (q : ℕ)) x).det) := by
    filter_upwards [hall] with x hx
    rw [integrand_eq]
    refine mul_nonneg (Finset.prod_nonneg fun j _ => (hw _ (Set.mem_Ioi.mp (hx j))).le) ?_
    exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ =>
      pair_nonneg_of_strictMonoOn ψ hψ (Set.mem_Ioi.mp (hx j)) (Set.mem_Ioi.mp (hx i))
  -- the support contains a box of positive measure
  have hBsub : Set.pi Set.univ (fun j : Fin k => Set.Ioo (((j : ℕ) : ℝ) + 1) (((j : ℕ) : ℝ) + 2))
      ⊆ Function.support (fun x : Fin k → ℝ =>
        (evalMatrix (fun (p : Fin k) (s : ℝ) => s ^ (p : ℕ) * w s) x).det *
        (evalMatrix (fun (q : Fin k) (s : ℝ) => ψ s ^ (q : ℕ)) x).det) := by
    intro x hx
    have hx' : ∀ j : Fin k, x j ∈ Set.Ioo (((j : ℕ) : ℝ) + 1) (((j : ℕ) : ℝ) + 2) :=
      fun j => Set.mem_pi.mp hx j (Set.mem_univ j)
    have hpos : ∀ j : Fin k, 0 < x j := by
      intro j
      have h1 := (hx' j).1
      have h2 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hlt : ∀ i j : Fin k, i < j → x i < x j := by
      intro i j hij
      have h1 := (hx' i).2
      have h2 := (hx' j).1
      have hn : (i : ℕ) + 1 ≤ (j : ℕ) := hij
      have hc : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hn
      linarith
    show x ∈ Function.support _
    rw [Function.mem_support, integrand_eq]
    refine (mul_pos (Finset.prod_pos fun j _ => hw _ (hpos j))
      (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_)).ne'
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact mul_pos (sub_pos.mpr (hlt i j hij))
      (sub_pos.mpr (hψ (Set.mem_Ioi.mpr (hpos i)) (Set.mem_Ioi.mpr (hpos j)) (hlt i j hij)))
  have hmeas : 0 < (Measure.pi fun _ : Fin k => μ)
      (Set.pi Set.univ (fun j : Fin k => Set.Ioo (((j : ℕ) : ℝ) + 1) (((j : ℕ) : ℝ) + 2))) := by
    rw [Measure.pi_pi]
    have hone : ∀ j : Fin k,
        μ (Set.Ioo (((j : ℕ) : ℝ) + 1) (((j : ℕ) : ℝ) + 2)) = 1 := by
      intro j
      have hsub : Set.Ioo (((j : ℕ) : ℝ) + 1) (((j : ℕ) : ℝ) + 2) ⊆ Set.Ioi (0 : ℝ) := by
        intro x hx
        have h0 : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
        exact lt_trans h0 hx.1
      rw [hμ, Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub,
        Real.volume_Ioo, show ((j : ℕ) : ℝ) + 2 - (((j : ℕ) : ℝ) + 1) = 1 by ring,
        ENNReal.ofReal_one]
    simp [hone]
  -- the integral of the nonnegative integrand is positive
  have hI := (integral_pos_iff_support_of_nonneg_ae hnn hfi).mpr
    (lt_of_lt_of_le hmeas (measure_mono hBsub))
  have hpos : 0 < (k.factorial : ℝ) *
      (Matrix.of fun p q : Fin k =>
        ∫ s in Set.Ioi (0 : ℝ), (s ^ (p : ℕ) * w s) * ψ s ^ (q : ℕ)).det := by
    rw [hkey]
    exact hI
  exact pos_of_mul_pos_right hpos (Nat.cast_nonneg _)

end Painleve
