import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
# Andréief's identity

For a σ-finite measure `μ` and real functions `φ_p, ψ_q` (`p, q < k`) whose
products are `μ`-integrable,
`k! · det[∫ φ_p ψ_q dμ] = ∫ det[φ_p(x_j)] · det[ψ_q(x_j)] dμ^k`.
This is the identity used in `eq:andreief` of `paper.tex`
(Andréief 1886; Forrester 2019, Section 2).
-/

open MeasureTheory Matrix Equiv

namespace Painleve

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]

/-- The matrix `[φ_p(x_j)]_{p,j}`. -/
def evalMatrix {k : ℕ} (φ : Fin k → α → ℝ) (x : Fin k → α) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun p j => φ p (x j)

/-- First (asymmetric) form: `det[∫ φ_p ψ_q] = ∫ (∏_i ψ_i(x_i)) det[φ_p(x_j)]`. -/
theorem andreief_asym {k : ℕ} (φ ψ : Fin k → α → ℝ)
    (hint : ∀ p q, Integrable (fun x => φ p x * ψ q x) μ) :
    (Matrix.of fun p q => ∫ x, φ p x * ψ q x ∂μ).det =
      ∫ x : Fin k → α, (∏ i, ψ i (x i)) * (evalMatrix φ x).det ∂(Measure.pi fun _ => μ) := by
  have hpt : ∀ x : Fin k → α, (∏ i, ψ i (x i)) * (evalMatrix φ x).det =
      ∑ σ : Perm (Fin k), (Perm.sign σ : ℝ) * ∏ i, (φ (σ i) (x i) * ψ i (x i)) := by
    intro x
    rw [det_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [evalMatrix, Matrix.of_apply, Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
    ring
  rw [det_apply]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
    rw [integral_const_mul]
    congr 1
    exact (integral_fintype_prod_eq_prod (fun i x => φ (σ i) x * ψ i x)).symm
  · intro σ _
    exact (Integrable.fintype_prod (f := fun i x => φ (σ i) x * ψ i x)
      (fun i => hint (σ i) i)).const_mul _

/-- Integrability of the asymmetric integrand. -/
theorem integrable_andreief_asym {k : ℕ} (φ ψ : Fin k → α → ℝ)
    (hint : ∀ p q, Integrable (fun x => φ p x * ψ q x) μ) :
    Integrable (fun x : Fin k → α => (∏ i, ψ i (x i)) * (evalMatrix φ x).det)
      (Measure.pi fun _ => μ) := by
  have hpt : ∀ x : Fin k → α, (∏ i, ψ i (x i)) * (evalMatrix φ x).det =
      ∑ σ : Perm (Fin k), (Perm.sign σ : ℝ) * ∏ i, (φ (σ i) (x i) * ψ i (x i)) := by
    intro x
    rw [det_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [evalMatrix, Matrix.of_apply, Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
    ring
  simp_rw [hpt]
  exact integrable_finsetSum _ fun σ _ =>
    (Integrable.fintype_prod (f := fun i x => φ (σ i) x * ψ i x)
      (fun i => hint (σ i) i)).const_mul _

/-- Permuting the points permutes the columns of `[φ_p(x_j)]`. -/
theorem det_evalMatrix_comp {k : ℕ} (φ : Fin k → α → ℝ) (x : Fin k → α) (τ : Perm (Fin k)) :
    (evalMatrix φ (fun i => x (τ i))).det = Perm.sign τ * (evalMatrix φ x).det := by
  have : evalMatrix φ (fun i => x (τ i)) = (evalMatrix φ x).submatrix id τ := by
    ext p j; rfl
  rw [this, det_permute']

/-- `Σ_τ sign τ ∏_i ψ_i(x_{τ i}) = det[ψ_q(x_j)]`. -/
theorem sum_sign_prod_eq_det {k : ℕ} (ψ : Fin k → α → ℝ) (x : Fin k → α) :
    ∑ τ : Perm (Fin k), (Perm.sign τ : ℝ) * ∏ i, ψ i (x (τ i)) = (evalMatrix ψ x).det := by
  rw [← det_transpose, det_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, evalMatrix, Matrix.transpose_apply, Matrix.of_apply]

/-- Relabelling the coordinates of a point by a permutation. -/
theorem piCongrLeft_perm_apply {k : ℕ} (τ : Perm (Fin k)) (x : Fin k → α) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin k => α) τ.symm) x = fun i => x (τ i) := by
  funext i
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp

/-- **Andréief's identity.** -/
theorem andreief {k : ℕ} (φ ψ : Fin k → α → ℝ)
    (hint : ∀ p q, Integrable (fun x => φ p x * ψ q x) μ) :
    (k.factorial : ℝ) * (Matrix.of fun p q => ∫ x, φ p x * ψ q x ∂μ).det =
      ∫ x : Fin k → α, (evalMatrix φ x).det * (evalMatrix ψ x).det
        ∂(Measure.pi fun _ => μ) := by
  set F : (Fin k → α) → ℝ := fun x => (∏ i, ψ i (x i)) * (evalMatrix φ x).det with hF
  have hFi : Integrable F (Measure.pi fun _ => μ) := integrable_andreief_asym μ φ ψ hint
  have hcomp : ∀ τ : Perm (Fin k),
      ∫ x : Fin k → α, F (fun i => x (τ i)) ∂(Measure.pi fun _ => μ) =
        ∫ x : Fin k → α, F x ∂(Measure.pi fun _ => μ) := by
    intro τ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin k => μ) τ.symm
    have := hmp.integral_comp' (g := F)
    simp only [piCongrLeft_perm_apply] at this
    exact this
  have hcompi : ∀ τ : Perm (Fin k),
      Integrable (fun x : Fin k → α => F (fun i => x (τ i))) (Measure.pi fun _ => μ) := by
    intro τ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin k => μ) τ.symm
    have := hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hFi
    simp only [Function.comp_def, piCongrLeft_perm_apply] at this
    exact this
  have hsum : ∀ x : Fin k → α, ∑ τ : Perm (Fin k), F (fun i => x (τ i)) =
      (evalMatrix φ x).det * (evalMatrix ψ x).det := by
    intro x
    simp only [hF, det_evalMatrix_comp]
    rw [← sum_sign_prod_eq_det ψ x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  calc (k.factorial : ℝ) * (Matrix.of fun p q => ∫ x, φ p x * ψ q x ∂μ).det
      = ∑ _τ : Perm (Fin k), ∫ x : Fin k → α, F x ∂(Measure.pi fun _ => μ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, andreief_asym μ φ ψ hint]
    _ = ∑ τ : Perm (Fin k), ∫ x : Fin k → α, F (fun i => x (τ i)) ∂(Measure.pi fun _ => μ) := by
        exact Finset.sum_congr rfl fun τ _ => (hcomp τ).symm
    _ = ∫ x : Fin k → α, ∑ τ : Perm (Fin k), F (fun i => x (τ i)) ∂(Measure.pi fun _ => μ) :=
        (integral_finsetSum _ fun τ _ => hcompi τ).symm
    _ = _ := by simp_rw [hsum]

/-- Integrability of the symmetric Andréief integrand. -/
theorem integrable_andreief {k : ℕ} (φ ψ : Fin k → α → ℝ)
    (hint : ∀ p q, Integrable (fun x => φ p x * ψ q x) μ) :
    Integrable (fun x : Fin k → α => (evalMatrix φ x).det * (evalMatrix ψ x).det)
      (Measure.pi fun _ => μ) := by
  set F : (Fin k → α) → ℝ := fun x => (∏ i, ψ i (x i)) * (evalMatrix φ x).det with hF
  have hFi : Integrable F (Measure.pi fun _ => μ) := integrable_andreief_asym μ φ ψ hint
  have hcompi : ∀ τ : Perm (Fin k),
      Integrable (fun x : Fin k → α => F (fun i => x (τ i))) (Measure.pi fun _ => μ) := by
    intro τ
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin k => μ) τ.symm
    have := hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hFi
    simp only [Function.comp_def, piCongrLeft_perm_apply] at this
    exact this
  have hsum : ∀ x : Fin k → α, ∑ τ : Perm (Fin k), F (fun i => x (τ i)) =
      (evalMatrix φ x).det * (evalMatrix ψ x).det := by
    intro x
    simp only [hF, det_evalMatrix_comp]
    rw [← sum_sign_prod_eq_det ψ x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  simp_rw [← hsum]
  exact integrable_finsetSum _ fun τ _ => hcompi τ

end Painleve
