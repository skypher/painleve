import Painleve.KernelDeriv
import Painleve.ExpTP
import Painleve.SymPos
import Painleve.Andreief
import Painleve.GammaLaw

/-!
# Signs of the Hankel determinants (Lemma 5.1 of `paper.tex`)

For shapes `β_1, …, β_m > 0` (`m ≥ 1`) let
`φ(u) = E[exp(-e^u G_1 ⋯ G_m)] = ∫ exp(-e^{u+y}) d(prodLaw βs)(y)`. Then
`(-1)^{k(k-1)/2} det[φ^{(p+q)}(u)]_{p,q<k} > 0` for every `u` and `k`.

`φ_0(u) = exp(-e^u)` and `φ_j = T_{β_j} φ_{j-1}`, with
`(T_β f)(u) = ∫ f(w) q_β(w-u) dw`. The claim
`sgn det[φ_j^{(p)}(u_l)] = (-1)^{k(k-1)/2}` for `u_1 < ⋯ < u_k` follows by
induction from Andréief's identity, the symmetry of the integrand, and the
strict total positivity of `q_β(w-u) ∝ e^{βw} e^{-βu} exp(ξζ)`, `ξ = e^w`,
`ζ = -e^{-u}`. The Hankel determinant at a single point is handled the same
way after moving the `q`-derivatives onto the kernel, where they produce monic
polynomials in `e^{w-u}`.
-/

open MeasureTheory Set Filter Matrix
open scoped ContDiff

namespace Painleve

/-- `φ_{βs}(u) = E[exp(-e^u ∏ G_j)]`. -/
noncomputable def phiL (βs : List ℝ) (u : ℝ) : ℝ :=
  ∫ y, Real.exp (-Real.exp (u + y)) ∂(prodLaw βs)

lemma phiL_nil : phiL [] = expKerFn 0 1 := by
  funext u
  unfold phiL expKerFn
  rw [prodLaw, integral_dirac]
  simp

lemma phiL_cons (β : ℝ) (βs : List ℝ) (hβ : 0 < β) (hβs : ∀ b ∈ βs, 0 < b) :
    phiL (β :: βs) = convT β (phiL βs) := by
  funext u
  haveI := isProbabilityMeasure_logGammaLaw' hβ
  haveI := isProbabilityMeasure_prodLaw βs hβs
  have hint : Integrable (fun z => Real.exp (-Real.exp (u + z))) (logGammaLaw β ∗ prodLaw βs) := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Real.exp_pos _).le
  unfold phiL convT
  rw [prodLaw, integral_conv hint, integral_logGammaLaw hβ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [add_assoc]

theorem smoothBdd_phiL : ∀ (βs : List ℝ), (∀ b ∈ βs, 0 < b) → SmoothBdd (phiL βs)
  | [], _ => by rw [phiL_nil]; exact smoothBdd_base
  | β :: βs, h => by
    have hβ : 0 < β := h β (by simp)
    have hβs : ∀ b ∈ βs, 0 < b := fun b hb => h b (by simp [hb])
    rw [phiL_cons β βs hβ hβs]
    exact (smoothBdd_phiL βs hβs).convT hβ

/-! ### The Andréief sign argument -/

/-- Andréief's identity with a symmetric sign pattern gives a strict sign. -/
theorem andreief_sign {k : ℕ} (φ ψ : Fin k → ℝ → ℝ)
    (hint : ∀ p q, Integrable (fun x => φ p x * ψ q x)) (s : ℝ)
    (hφ : ∀ w : Fin k → ℝ, StrictMono w → 0 < s * (evalMatrix φ w).det)
    (hψ : ∀ w : Fin k → ℝ, StrictMono w → 0 < (evalMatrix ψ w).det) :
    0 < s * (Matrix.of fun p q => ∫ x, φ p x * ψ q x).det := by
  have hA := andreief (volume : Measure ℝ) φ ψ hint
  have hI := integrable_andreief (volume : Measure ℝ) φ ψ hint
  have hvol : (Measure.pi fun _ : Fin k => (volume : Measure ℝ)) = volume := rfl
  rw [hvol] at hA hI
  have hpos := integral_pos_of_sym (fun w => (evalMatrix φ w).det * (evalMatrix ψ w).det) hI s
    (fun σ w => by
      show (evalMatrix φ (fun i => w (σ i))).det * (evalMatrix ψ (fun i => w (σ i))).det = _
      rw [det_evalMatrix_comp, det_evalMatrix_comp]
      have : (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ) = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      linear_combination ((evalMatrix φ w).det * (evalMatrix ψ w).det) * this)
    (fun w hw => by
      have := mul_pos (hφ w hw) (hψ w hw)
      linarith [show s * ((evalMatrix φ w).det * (evalMatrix ψ w).det)
        = s * (evalMatrix φ w).det * (evalMatrix ψ w).det by ring])
  rw [← hA] at hpos
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have : s * ((k.factorial : ℝ) * (Matrix.of fun p q => ∫ x, φ p x * ψ q x).det)
      = (k.factorial : ℝ) * (s * (Matrix.of fun p q => ∫ x, φ p x * ψ q x).det) := by ring
  rw [this] at hpos
  exact pos_of_mul_pos_right hpos hk.le

/-- `[f^{(p)}(u_l)]_{p,l}`. -/
noncomputable def derivMat (f : ℝ → ℝ) {k : ℕ} (u : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun p l => iteratedDeriv p f (u l)

lemma det_scale_cols {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (e : Fin k → ℝ) :
    (Matrix.of fun p l => A p l * e l).det = A.det * ∏ l, e l := by
  have : (Matrix.of fun p l => A p l * e l) = A * Matrix.diagonal e := by
    ext p l; simp [Matrix.mul_diagonal]
  rw [this, Matrix.det_mul, Matrix.det_diagonal]

lemma det_scale_rows {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (e : Fin k → ℝ) :
    (Matrix.of fun p l => e p * A p l).det = (∏ p, e p) * A.det := by
  have : (Matrix.of fun p l => e p * A p l) = Matrix.diagonal e * A := by
    ext p l; simp [Matrix.diagonal_mul]
  rw [this, Matrix.det_mul, Matrix.det_diagonal]

lemma neg_one_pow_sq (n : ℕ) : ((-1 : ℝ) ^ n) * ((-1) ^ n) = 1 := by
  rw [← mul_pow]; norm_num

/-- Base case: `φ_0 = exp(-e^u)`. -/
theorem claim_nil {k : ℕ} (u : Fin k → ℝ) (hu : StrictMono u) :
    0 < (-1 : ℝ) ^ (k * (k - 1) / 2) * (derivMat (expKerFn 0 1) u).det := by
  set x : Fin k → ℝ := fun l => Real.exp (u l)
  have hx : StrictMono x := fun l m h => Real.exp_lt_exp.mpr (hu h)
  have hmat : derivMat (expKerFn 0 1) u
      = Matrix.of fun p l => (Matrix.of fun (i q : Fin k) => (derPoly 0 1 q).eval (x i))ᵀ p l *
          expKerFn 0 1 (u l) := by
    ext p l
    simp only [derivMat, Matrix.of_apply, Matrix.transpose_apply, iteratedDeriv_expKerFn, x]
    ring
  rw [hmat, det_scale_cols, Matrix.det_transpose, det_derPoly]
  have hV := det_vandermonde_pos x hx
  have hE : 0 < ∏ l, expKerFn 0 1 (u l) := Finset.prod_pos fun l _ => Real.exp_pos _
  have hsq := neg_one_pow_sq (k * (k - 1) / 2)
  rw [show (-(1 : ℝ)) = -1 from rfl]
  nlinarith [mul_pos hV hE]

lemma iteratedDeriv_convT_at {β : ℝ} (hβ : 0 < β) {f : ℝ → ℝ} (hf : SmoothBdd f) (p : ℕ)
    (u : ℝ) : iteratedDeriv p (convT β f) u = ∫ w, iteratedDeriv p f w * qLog β (w - u) := by
  rw [iteratedDeriv_convT hβ hf p, convT_eq_kernel]

lemma integrable_bdd_mul_qLog {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (u : ℝ) : Integrable (fun w => g w * qLog β (w - u)) := by
  refine Integrable.mono' (((integrable_qLog hβ).comp_sub_right u).const_mul C)
    (hg.aestronglyMeasurable.mul
      ((measurable_qLog β).comp (measurable_id.sub_const u)).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (qLog_nonneg hβ _)]
  exact mul_le_mul_of_nonneg_right (hC w) (qLog_nonneg hβ _)

/-- `det[q_β(w_j - u_l)]_{l,j} > 0` for increasing `w` and `u`. -/
lemma det_qLog_shift_pos {β : ℝ} (hβ : 0 < β) {k : ℕ} (u w : Fin k → ℝ) (hu : StrictMono u)
    (hw : StrictMono w) :
    0 < (evalMatrix (fun l x => qLog β (x - u l)) w).det := by
  set ξ : Fin k → ℝ := fun j => Real.exp (w j)
  set ζ : Fin k → ℝ := fun l => -Real.exp (-u l)
  have hξ : StrictMono ξ := fun i j h => Real.exp_lt_exp.mpr (hw h)
  have hζ : StrictMono ζ := fun i j h => by
    simp only [ζ, neg_lt_neg_iff]
    exact Real.exp_lt_exp.mpr (neg_lt_neg (hu h))
  have hG : 0 < Real.Gamma β := Real.Gamma_pos_of_pos hβ
  set M : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun l j => expKer ζ ξ l j * (Real.exp (β * w j) / Real.Gamma β) with hM
  have hmat : evalMatrix (fun l x => qLog β (x - u l)) w
      = Matrix.of fun l j => Real.exp (-(β * u l)) * M l j := by
    ext l j
    simp only [evalMatrix, Matrix.of_apply, hM, expKer, qLog, ξ, ζ]
    have he : Real.exp (w j - u l) = Real.exp (-u l) * Real.exp (w j) := by
      rw [← Real.exp_add]; ring_nf
    rw [he, show β * (w j - u l) - Real.exp (-u l) * Real.exp (w j)
        = -(β * u l) + (β * w j + -Real.exp (-u l) * Real.exp (w j)) by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hMdet : M.det = (expKer ζ ξ).det * ∏ j, (Real.exp (β * w j) / Real.Gamma β) := by
    rw [hM]; exact det_scale_cols (expKer ζ ξ) (fun j => Real.exp (β * w j) / Real.Gamma β)
  rw [hmat, det_scale_rows, hMdet]
  exact mul_pos (Finset.prod_pos fun l _ => Real.exp_pos _)
    (mul_pos (det_expKer_pos ζ ξ hζ hξ) (Finset.prod_pos fun j _ => div_pos (Real.exp_pos _) hG))

/-- **The claim** of `lem:hankel-signs`: `sgn det[φ^{(p)}(u_l)] = (-1)^{k(k-1)/2}`. -/
theorem claim_phiL : ∀ (βs : List ℝ), (∀ b ∈ βs, 0 < b) → ∀ {k : ℕ} (u : Fin k → ℝ),
    StrictMono u → 0 < (-1 : ℝ) ^ (k * (k - 1) / 2) * (derivMat (phiL βs) u).det
  | [], _, k, u, hu => by rw [phiL_nil]; exact claim_nil u hu
  | β :: βs, h, k, u, hu => by
    have hβ : 0 < β := h β (by simp)
    have hβs : ∀ b ∈ βs, 0 < b := fun b hb => h b (by simp [hb])
    have hf := smoothBdd_phiL βs hβs
    rw [phiL_cons β βs hβ hβs]
    have hmat : derivMat (convT β (phiL βs)) u
        = Matrix.of fun p l => ∫ x, (fun (p : Fin k) w => iteratedDeriv p (phiL βs) w) p x *
            (fun (l : Fin k) x => qLog β (x - u l)) l x := by
      ext p l
      simp only [derivMat, Matrix.of_apply]
      exact iteratedDeriv_convT_at hβ hf p (u l)
    rw [hmat]
    refine andreief_sign _ _ (fun p q => ?_) _ (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨C, hC⟩ := hf.2 p
      exact integrable_bdd_mul_qLog hβ (hf.continuous_iteratedDeriv p) hC (u q)
    · exact claim_phiL βs hβs w hw
    · exact det_qLog_shift_pos hβ u w hu hw

lemma iteratedDeriv_add_eq (f : ℝ → ℝ) (p q : ℕ) :
    iteratedDeriv (p + q) f = iteratedDeriv q (iteratedDeriv p f) := by
  induction q with
  | zero => simp
  | succ q ih => rw [← add_assoc, iteratedDeriv_succ, ih, iteratedDeriv_succ]

/-- **Lemma 5.1** (`lem:hankel-signs`). -/
theorem hankel_sign (β : ℝ) (βs : List ℝ) (hβ : 0 < β) (hβs : ∀ b ∈ βs, 0 < b) (u : ℝ)
    (k : ℕ) :
    0 < (-1 : ℝ) ^ (k * (k - 1) / 2) *
      (Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q) (phiL (β :: βs)) u).det := by
  have hf := smoothBdd_phiL βs hβs
  rw [phiL_cons β βs hβ hβs]
  -- `(-1)^q q_β^{(q)}(v) = q_β(v) Q_q(e^v)` with `Q_q = (-1)^q P_q` monic
  set Q : ℕ → Polynomial ℝ := fun q => Polynomial.C ((-1 : ℝ) ^ q) * derPoly β 1 q with hQ
  have hker : ∀ (q : ℕ) (v : ℝ), (-1 : ℝ) ^ q * iteratedDeriv q (qLog β) v
      = qLog β v * (Q q).eval (Real.exp v) := by
    intro q v
    rw [iteratedDeriv_qLog]
    simp only [hQ, Polynomial.eval_mul, Polynomial.eval_C, qLog, expKerFn]
    ring
  have hmat : (Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q) (convT β (phiL βs)) u)
      = Matrix.of fun p q => ∫ x, (fun (p : Fin k) w => iteratedDeriv p (phiL βs) w) p x *
          (fun (q : Fin k) w => qLog β (w - u) * (Q q).eval (Real.exp (w - u))) q x := by
    ext p q
    simp only [Matrix.of_apply]
    rw [iteratedDeriv_add_eq, iteratedDeriv_convT hβ hf p]
    obtain ⟨C, hC⟩ := hf.2 p
    rw [iteratedDeriv_convT_kernel hβ (hf.continuous_iteratedDeriv p) hC q]
    simp only [hker]
  rw [hmat]
  refine andreief_sign _ _ (fun p q => ?_) _ (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨C, hC⟩ := hf.2 p
    obtain ⟨D, hD⟩ := bdd_poly_mul_exp (Q q) (c := 1 / 2) (by norm_num)
    -- `|q_β(v) Q(e^v)| ≤ D' q_{β}`-type bound via `kernel_bound`
    obtain ⟨B, hBi, hB⟩ := kernel_bound hβ q u
    refine Integrable.mono' (hBi.const_mul C) ?_ (Eventually.of_forall fun w => ?_)
    · refine ((hf.continuous_iteratedDeriv p).aestronglyMeasurable).mul ?_
      refine Continuous.aestronglyMeasurable ?_
      have : (fun w => qLog β (w - u) * (Q q).eval (Real.exp (w - u)))
          = fun w => (-1 : ℝ) ^ (q : ℕ) * iteratedDeriv q (qLog β) (w - u) := by
        funext w; rw [hker]
      rw [this]
      exact continuous_const.mul (((contDiff_qLog β).continuous_iteratedDeriv q
        (by exact_mod_cast WithTop.coe_le_coe.mpr le_top)).comp (continuous_id.sub continuous_const))
    · rw [Real.norm_eq_abs, abs_mul, ← hker, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul (hC w) (hB u (Metric.mem_ball_self one_pos) w) (abs_nonneg _)
        ((abs_nonneg _).trans (hC 0))
  · exact claim_phiL βs hβs w hw
  · -- `det[q_β(w_j - u) Q_q(e^{w_j-u})]_{q,j} = ∏_j q_β(w_j - u) · V(e^{w-u})`
    set y : Fin k → ℝ := fun j => Real.exp (w j - u)
    have hy : StrictMono y := fun i j h => Real.exp_lt_exp.mpr (by linarith [hw h])
    have hQdeg : ∀ q, (Q q).natDegree ≤ q := fun q =>
      (Polynomial.natDegree_C_mul_le _ _).trans (derPoly_natDegree_le β 1 q)
    have hQlead : ∀ q, (Q q).coeff q = 1 := by
      intro q
      simp only [hQ, Polynomial.coeff_C_mul, derPoly_coeff_self]
      rw [← mul_pow]; norm_num
    have hmat2 : evalMatrix (fun (q : Fin k) w => qLog β (w - u) * (Q q).eval (Real.exp (w - u))) w
        = (Matrix.of fun (j q : Fin k) => (Q q).eval (y j) * qLog β (w j - u))ᵀ := by
      ext q j
      simp only [evalMatrix, Matrix.of_apply, Matrix.transpose_apply, y]
      ring
    rw [hmat2, Matrix.det_transpose]
    have hrow : (Matrix.of fun (j q : Fin k) => (Q q).eval (y j) * qLog β (w j - u))
        = Matrix.of fun j q => qLog β (w j - u) * (Matrix.of fun (i q : Fin k) => (Q q).eval (y i)) j q := by
      ext j q; simp only [Matrix.of_apply]; ring
    rw [hrow, det_scale_rows, det_eval_polys Q hQdeg y]
    simp only [hQlead, Finset.prod_const_one, one_mul]
    exact mul_pos (Finset.prod_pos fun j _ => qLog_pos hβ _) (det_vandermonde_pos y hy)

end Painleve
