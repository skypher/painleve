import Painleve.Kernel
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace Painleve
open MeasureTheory
open scoped ContDiff

noncomputable def Phi (α β y w : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + w * s ^ 2) ^ (-(β + 1 / 2))

noncomputable def Bmom (α β y : ℝ) (p q : ℕ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), s ^ p * (s ^ 2 / (1 + s ^ 2)) ^ q *
    (Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2)))

/-- The auxiliary integral `∫_{s>0} e^{-ys} s^{α-1/2} s^k (1+ws²)^p`. -/
noncomputable def Gw (α y : ℝ) (k : ℕ) (p w : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k * (1 + w * s ^ 2) ^ p

lemma kernel_pow_integrable (α y w : ℝ) (k : ℕ) (p : ℝ) (hy : 0 < y) (hw : 0 < w)
    (hα : 0 ≤ α) :
    IntegrableOn (fun s : ℝ => Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k *
      (1 + w * s ^ 2) ^ p) (Set.Ioi 0) := by
  have h := integrableOn_kernel y w (α + k) (-p - 1 / 2) hy hw (by positivity)
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := hs
  have hp : -(-p - 1 / 2 + 1 / 2) = p := by ring
  have hpow : α + (k : ℝ) - 1 / 2 = (α - 1 / 2) + (k : ℝ) := by ring
  simp only [hp, hpow]
  rw [Real.rpow_add hs0, Real.rpow_natCast]
  ring

/-- Comparison of `(1 + w s²)^c` with `(1 + s²)^c` for `w` in a compact range. -/
lemma rpow_one_add_sq_le (c w0 w s : ℝ) (hw0 : 0 < w0) (hw1 : w0 / 2 < w) (hw2 : w < 2 * w0) :
    (1 + w * s ^ 2) ^ c ≤ ((min 1 (w0 / 2)) ^ c + (max 1 (2 * w0)) ^ c) * (1 + s ^ 2) ^ c := by
  set m := min 1 (w0 / 2) with hm
  set M := max 1 (2 * w0) with hM
  have hm0 : 0 < m := lt_min one_pos (by linarith)
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hmX : m * (1 + s ^ 2) ≤ 1 + w * s ^ 2 := by
    have h1 : m ≤ 1 := min_le_left _ _
    have h2 : m ≤ w0 / 2 := min_le_right _ _
    have h3 : m * s ^ 2 ≤ w * s ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
    nlinarith
  have hXM : 1 + w * s ^ 2 ≤ M * (1 + s ^ 2) := by
    have h1 : 1 ≤ M := le_max_left _ _
    have h2 : 2 * w0 ≤ M := le_max_right _ _
    have h3 : w * s ^ 2 ≤ M * s ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
    nlinarith
  have hX : 0 < 1 + s ^ 2 := by positivity
  have hB : 0 < 1 + w * s ^ 2 := by
    have : 0 < w := by linarith
    positivity
  have hMc : 0 < M ^ c := Real.rpow_pos_of_pos hM0 c
  have hmc : 0 < m ^ c := Real.rpow_pos_of_pos hm0 c
  have hXc : 0 ≤ (1 + s ^ 2) ^ c := Real.rpow_nonneg hX.le c
  rcases le_total 0 c with hc | hc
  · calc (1 + w * s ^ 2) ^ c ≤ (M * (1 + s ^ 2)) ^ c := Real.rpow_le_rpow hB.le hXM hc
      _ = M ^ c * (1 + s ^ 2) ^ c := Real.mul_rpow hM0.le hX.le
      _ ≤ (m ^ c + M ^ c) * (1 + s ^ 2) ^ c := by
          rw [add_mul]; linarith [mul_nonneg hmc.le hXc]
  · calc (1 + w * s ^ 2) ^ c ≤ (m * (1 + s ^ 2)) ^ c :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hm0 hX) hmX hc
      _ = m ^ c * (1 + s ^ 2) ^ c := Real.mul_rpow hm0.le hX.le
      _ ≤ (m ^ c + M ^ c) * (1 + s ^ 2) ^ c := by
          rw [add_mul]; linarith [mul_nonneg hMc.le hXc]

/-- Derivative in `w` of `Gw`, at `w0 > 0`. -/
lemma hasDerivAt_Gw (α y : ℝ) (hy : 0 < y) (hα : 0 ≤ α) (k : ℕ) (p : ℝ) (w0 : ℝ)
    (hw0 : 0 < w0) :
    HasDerivAt (Gw α y k p)
      (∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k *
        (p * (s ^ 2 * (1 + w0 * s ^ 2) ^ (p - 1)))) w0 := by
  unfold Gw
  set U := Set.Ioo (w0 / 2) (2 * w0) with hUdef
  have hw0U : w0 ∈ U := ⟨by linarith, by linarith⟩
  set K := (min 1 (w0 / 2)) ^ (p - 1) + (max 1 (2 * w0)) ^ (p - 1) with hK
  have hKnn : 0 ≤ K := by
    have h1 : 0 < min 1 (w0 / 2) := lt_min one_pos (by linarith)
    have h2 : 0 < max 1 (2 * w0) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have := Real.rpow_pos_of_pos h1 (p - 1)
    have := Real.rpow_pos_of_pos h2 (p - 1)
    positivity
  have hbound_int : Integrable (fun s : ℝ => (|p| * K) *
      (Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (k + 2) * (1 + 1 * s ^ 2) ^ (p - 1)))
      (volume.restrict (Set.Ioi 0)) := by
    have h := (kernel_pow_integrable α y 1 (k + 2) (p - 1) hy one_pos hα).const_mul (|p| * K)
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [pow_add]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0))
    (F := fun w s => Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k * (1 + w * s ^ 2) ^ p)
    (F' := fun w s => Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k *
        (p * (s ^ 2 * (1 + w * s ^ 2) ^ (p - 1))))
    (x₀ := w0) (s := U) (bound := fun s => (|p| * K) *
      (Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (k + 2) * (1 + 1 * s ^ 2) ^ (p - 1)))
    (isOpen_Ioo.mem_nhds hw0U) ?_ ?_ ?_ ?_ hbound_int ?_).2
  · refine Filter.Eventually.of_forall fun w => ?_
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact kernel_pow_integrable α y w0 k p hy hw0 hα
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs w hw => ?_)
    have hs0 : 0 < s := hs
    have hwpos : 0 < w := by linarith [hw.1]
    have hcmp : (1 + w * s ^ 2) ^ (p - 1) ≤ K * (1 + s ^ 2) ^ (p - 1) :=
      rpow_one_add_sq_le (p - 1) w0 w s hw0 hw.1 hw.2
    have hE : 0 ≤ Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k := by positivity
    have hEs2 : 0 ≤ Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k * s ^ 2 := by positivity
    have hB : 0 ≤ (1 + w * s ^ 2) ^ (p - 1) := Real.rpow_nonneg (by positivity) _
    have heq : Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k *
        (p * (s ^ 2 * (1 + w * s ^ 2) ^ (p - 1)))
        = p * ((Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k * s ^ 2) *
          (1 + w * s ^ 2) ^ (p - 1)) := by ring
    simp only [one_mul, pow_add]
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hEs2 hB)]
    have key := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hEs2) (abs_nonneg p)
    exact le_trans (le_of_eq (by ring)) (le_trans key (le_of_eq (by ring)))
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs w hw => ?_)
    have hs0 : 0 < s := hs
    have hwpos : 0 < w := by linarith [hw.1]
    have hpos : 0 < 1 + w * s ^ 2 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => 1 + x * s ^ 2) (s ^ 2) w := by
      simpa using ((hasDerivAt_id' w).mul_const (s ^ 2)).const_add 1
    have h2 := h1.rpow_const (p := p) (Or.inl hpos.ne')
    have h3 := h2.const_mul (Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ k)
    exact h3.congr_deriv (by ring)

/-- The explicit `j`-th `w`-derivative formula, as a function of `w`. -/
noncomputable def PsiW (α β y : ℝ) (j : ℕ) (w : ℝ) : ℝ :=
  (-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) *
    Gw α y (2 * j) (-(β + 1 / 2) - (j : ℝ)) w

lemma PsiW_hasDerivAt (α β y : ℝ) (hy : 0 < y) (hα : 0 ≤ α) (j : ℕ) (w0 : ℝ) (hw0 : 0 < w0) :
    HasDerivAt (PsiW α β y j) (PsiW α β y (j + 1) w0) w0 := by
  have h := (hasDerivAt_Gw α y hy hα (2 * j) (-(β + 1 / 2) - (j : ℝ)) w0 hw0).const_mul
    ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2))
  have hexp : (-(β + 1 / 2) - (j : ℝ)) - 1 = -(β + 1 / 2) - ((j + 1 : ℕ) : ℝ) := by
    push_cast; ring
  have hint : (∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
      ((-(β + 1 / 2) - (j : ℝ)) * (s ^ 2 * (1 + w0 * s ^ 2) ^ ((-(β + 1 / 2) - (j : ℝ)) - 1))))
      = (-(β + 1 / 2) - (j : ℝ)) * ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) *
          s ^ (2 * (j + 1)) * (1 + w0 * s ^ 2) ^ (-(β + 1 / 2) - ((j + 1 : ℕ) : ℝ)) := by
    rw [← integral_const_mul]
    congr 1
    funext s
    rw [hexp]
    ring
  have hc := ascPochhammer_succ_eval (S := ℝ) j (β + 1 / 2)
  show HasDerivAt (fun w => (-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) *
    Gw α y (2 * j) (-(β + 1 / 2) - (j : ℝ)) w) _ w0
  refine h.congr_deriv ?_
  unfold PsiW Gw
  rw [hint, hc]
  push_cast
  ring

lemma iteratedDeriv_Phi_eq (α β y : ℝ) (hy : 0 < y) (hα : 0 ≤ α) (j : ℕ) :
    ∀ w : ℝ, 0 < w → iteratedDeriv j (Phi α β y) w = PsiW α β y j w := by
  induction j with
  | zero =>
    intro w hw
    rw [iteratedDeriv_zero]
    simp [PsiW, Gw, Phi]
  | succ j ih =>
    intro w hw
    have hev : iteratedDeriv j (Phi α β y) =ᶠ[nhds w] PsiW α β y j :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hw) (fun u hu => ih u hu)
    rw [iteratedDeriv_succ, hev.deriv_eq, (PsiW_hasDerivAt α β y hy hα j w hw).deriv]

theorem iteratedDeriv_Phi (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (j : ℕ) (w : ℝ) (hw : 0 < w) :
    iteratedDeriv j (Phi α β y) w =
      (-1) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) *
        ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
          (1 + w * s ^ 2) ^ (-(β + 1 / 2) - j) := by
  rw [iteratedDeriv_Phi_eq α β y hy hα j w hw]
  simp only [PsiW, Gw]

/-- Differentiability of all iterated derivatives on an open set gives `C^∞` there. -/
theorem contDiffOn_of_iter_differentiable (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ m : ℕ, ∀ x ∈ U, DifferentiableAt ℝ (iteratedDeriv m f) x) :
    ContDiffOn ℝ ∞ f U := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m _ x hx
  exact ((h m x hx).differentiableWithinAt).congr
    (fun y hy => iteratedDerivWithin_of_isOpen hU hy) (iteratedDerivWithin_of_isOpen hU hx)

theorem Phi_contDiffOn (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) :
    ContDiffOn ℝ ∞ (Phi α β y) (Set.Ioi 0) := by
  apply contDiffOn_of_iter_differentiable _ isOpen_Ioi
  intro m x hx
  have hd := (PsiW_hasDerivAt α β y hy hα m x hx).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) (fun u hu => iteratedDeriv_Phi_eq α β y hy hα m u hu))
  exact hd.differentiableAt

/-- The rescaled kernel `g(t) = e^{-(y/c)t} t^{α-1/2} t^{2j} (1+t²)^{-(β+1/2)-j}`. -/
noncomputable def gScal (α β y c : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(y / c) * t) * t ^ (α - 1 / 2) * t ^ (2 * j) * (1 + t ^ 2) ^ (-(β + 1 / 2) - (j : ℝ))

theorem Phi_scaling (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (j : ℕ) (w : ℝ) (hw : 0 < w) :
    w ^ j * iteratedDeriv j (Phi α β y) w =
      (-1) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) *
        (w ^ (-(α / 2 + 1 / 4)) * Bmom α β (y * w ^ (-(1 / 2 : ℝ))) 0 j) := by
  have hc : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hc2 : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  set c := Real.sqrt w with hcdef
  rw [iteratedDeriv_Phi α β y hα hy j w hw]
  have h1 : w ^ j * ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
      (1 + w * s ^ 2) ^ (-(β + 1 / 2) - (j : ℝ))
      = c ^ (-(α - 1 / 2)) * ∫ s in Set.Ioi (0 : ℝ), gScal α β y c j (c * s) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := hs
    beta_reduce
    unfold gScal
    have hcs : (c * s) ^ (α - 1 / 2) = c ^ (α - 1 / 2) * s ^ (α - 1 / 2) :=
      Real.mul_rpow hc.le hs0.le
    have hcs2 : (c * s) ^ (2 * j) = w ^ j * s ^ (2 * j) := by
      rw [mul_pow, pow_mul, hc2]
    have hpt : (1 + (c * s) ^ 2) = 1 + w * s ^ 2 := by rw [mul_pow, hc2]
    have hE : Real.exp (-(y / c) * (c * s)) = Real.exp (-y * s) := by
      congr 1
      field_simp
    have hca : c ^ (-(α - 1 / 2)) * c ^ (α - 1 / 2) = 1 := by
      rw [← Real.rpow_add hc]; norm_num
    rw [hcs, hcs2, hpt, hE]
    linear_combination (-(w ^ j * (Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
      (1 + w * s ^ 2) ^ (-(β + 1 / 2) - (j : ℝ))))) * hca
  have h2 : ∫ s in Set.Ioi (0 : ℝ), gScal α β y c j (c * s)
      = c⁻¹ * ∫ t in Set.Ioi (0 : ℝ), gScal α β y c j t := by
    rw [integral_comp_mul_left_Ioi (fun t => gScal α β y c j t) 0 hc, mul_zero, smul_eq_mul]
  have h3 : ∫ t in Set.Ioi (0 : ℝ), gScal α β y c j t = Bmom α β (y / c) 0 j := by
    unfold Bmom
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    have hX : 0 < 1 + t ^ 2 := by positivity
    beta_reduce
    unfold gScal
    rw [pow_zero, one_mul, pow_mul, Real.rpow_sub hX, Real.rpow_natCast, div_pow]
    ring
  have h4 : w ^ (-(α / 2 + 1 / 4)) = c ^ (-(α - 1 / 2)) * c⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc, hcdef, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hw.le]
    congr 1
    ring
  have h5 : y * w ^ (-(1 / 2 : ℝ)) = y / c := by
    rw [Real.rpow_neg hw.le, ← Real.sqrt_eq_rpow, ← hcdef, div_eq_mul_inv]
  have key : w ^ j * ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
      (1 + w * s ^ 2) ^ (-(β + 1 / 2) - (j : ℝ))
      = c ^ (-(α - 1 / 2)) * (c⁻¹ * Bmom α β (y / c) 0 j) := by
    rw [h1, h2, h3]
  have hgoal : w ^ j * ((-1) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) *
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
        (1 + w * s ^ 2) ^ (-(β + 1 / 2) - (j : ℝ)))
      = (-1) ^ j * (ascPochhammer ℝ j).eval (β + 1 / 2) *
        (w ^ j * ∫ s in Set.Ioi (0 : ℝ), Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (2 * j) *
          (1 + w * s ^ 2) ^ (-(β + 1 / 2) - (j : ℝ))) := by ring
  rw [hgoal, key, h4, h5]
  ring

lemma bmom_bound_pt (α β y0 y : ℝ) (m q : ℕ) (_hα : 0 ≤ α) (_hy0 : 0 < y0) (hy : y0 / 2 ≤ y)
    (s : ℝ) (hs : 0 < s) :
    |s ^ m * (s ^ 2 / (1 + s ^ 2)) ^ q * (Real.exp (-y * s) * s ^ (α - 1 / 2) *
      (1 + s ^ 2) ^ (-(β + 1 / 2)))|
      ≤ Real.exp (-(y0 / 2) * s) * s ^ (α - 1 / 2) * s ^ m * (1 + s ^ 2) ^ (-(β + 1 / 2)) := by
  have hX : 0 < 1 + s ^ 2 := by positivity
  have hψ : (s ^ 2 / (1 + s ^ 2)) ^ q ≤ 1 :=
    pow_le_one₀ (div_nonneg (sq_nonneg s) hX.le) ((div_le_one hX).2 (by linarith [sq_nonneg s]))
  have he : Real.exp (-y * s) ≤ Real.exp (-(y0 / 2) * s) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hsa : 0 ≤ s ^ (α - 1 / 2) := Real.rpow_nonneg hs.le _
  have hXc : 0 ≤ (1 + s ^ 2) ^ (-(β + 1 / 2)) := Real.rpow_nonneg hX.le _
  have hsm : 0 ≤ s ^ m := pow_nonneg hs.le m
  have hψnn : 0 ≤ (s ^ 2 / (1 + s ^ 2)) ^ q := pow_nonneg (div_nonneg (sq_nonneg s) hX.le) q
  have hEnn : 0 ≤ Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2)) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hsa) hXc
  have hnn : 0 ≤ s ^ m * (s ^ 2 / (1 + s ^ 2)) ^ q * (Real.exp (-y * s) * s ^ (α - 1 / 2) *
      (1 + s ^ 2) ^ (-(β + 1 / 2))) := mul_nonneg (mul_nonneg hsm hψnn) hEnn
  rw [abs_of_nonneg hnn]
  have h1 : (s ^ 2 / (1 + s ^ 2)) ^ q * (Real.exp (-y * s) * s ^ (α - 1 / 2) *
      (1 + s ^ 2) ^ (-(β + 1 / 2))) ≤ 1 * (Real.exp (-(y0 / 2) * s) * s ^ (α - 1 / 2) *
      (1 + s ^ 2) ^ (-(β + 1 / 2))) :=
    mul_le_mul hψ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hsa) hXc)
      hEnn zero_le_one
  calc s ^ m * (s ^ 2 / (1 + s ^ 2)) ^ q * (Real.exp (-y * s) * s ^ (α - 1 / 2) *
        (1 + s ^ 2) ^ (-(β + 1 / 2)))
      = s ^ m * ((s ^ 2 / (1 + s ^ 2)) ^ q * (Real.exp (-y * s) * s ^ (α - 1 / 2) *
        (1 + s ^ 2) ^ (-(β + 1 / 2)))) := by ring
    _ ≤ s ^ m * (1 * (Real.exp (-(y0 / 2) * s) * s ^ (α - 1 / 2) *
        (1 + s ^ 2) ^ (-(β + 1 / 2)))) := mul_le_mul_of_nonneg_left h1 hsm
    _ = Real.exp (-(y0 / 2) * s) * s ^ (α - 1 / 2) * s ^ m * (1 + s ^ 2) ^ (-(β + 1 / 2)) := by
        ring

lemma bmom_bound_int (α β y0 : ℝ) (m : ℕ) (_hα : 0 ≤ α) (_hy0 : 0 < y0) :
    Integrable (fun s : ℝ => Real.exp (-(y0 / 2) * s) * s ^ (α - 1 / 2) * s ^ m *
      (1 + s ^ 2) ^ (-(β + 1 / 2))) (volume.restrict (Set.Ioi 0)) := by
  have h := kernel_pow_integrable α (y0 / 2) 1 m (-(β + 1 / 2)) (by linarith) one_pos _hα
  simp only [one_mul] at h
  exact h

/-- Derivative in `y` of `Bmom`. -/
lemma hasDerivAt_Bmom (α β : ℝ) (hα : 0 ≤ α) (p q : ℕ) (y0 : ℝ) (hy0 : 0 < y0) :
    HasDerivAt (fun y => Bmom α β y p q) (-Bmom α β y0 (p + 1) q) y0 := by
  have hy0U : y0 ∈ Set.Ioo (y0 / 2) (2 * y0) := ⟨by linarith, by linarith⟩
  have key : HasDerivAt
      (fun y => ∫ s in Set.Ioi (0 : ℝ), s ^ p * (s ^ 2 / (1 + s ^ 2)) ^ q *
        (Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2))))
      (∫ s in Set.Ioi (0 : ℝ), -(s ^ (p + 1) * (s ^ 2 / (1 + s ^ 2)) ^ q *
        (Real.exp (-y0 * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2))))) y0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := fun y s => s ^ p * (s ^ 2 / (1 + s ^ 2)) ^ q *
        (Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2))))
      (F' := fun y s => -(s ^ (p + 1) * (s ^ 2 / (1 + s ^ 2)) ^ q *
        (Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2)))))
      (x₀ := y0) (s := Set.Ioo (y0 / 2) (2 * y0))
      (bound := fun s => Real.exp (-(y0 / 2) * s) * s ^ (α - 1 / 2) * s ^ (p + 1) *
        (1 + s ^ 2) ^ (-(β + 1 / 2)))
      (isOpen_Ioo.mem_nhds hy0U) ?_ ?_ ?_ ?_ (bmom_bound_int α β y0 (p + 1) hα hy0) ?_).2
    · refine Filter.Eventually.of_forall fun y => ?_
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · refine Integrable.mono' (bmom_bound_int α β y0 p hα hy0)
        (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
      have hs0 : 0 < s := hs
      rw [Real.norm_eq_abs]
      exact bmom_bound_pt α β y0 y0 p q hα hy0 (by linarith) s hs0
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs y hy => ?_)
      have hs0 : 0 < s := hs
      rw [norm_neg, Real.norm_eq_abs]
      exact bmom_bound_pt α β y0 y (p + 1) q hα hy0 (le_of_lt hy.1) s hs0
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs y hy => ?_)
      have h1 : HasDerivAt (fun x : ℝ => -x * s) (-1 * s) y :=
        ((hasDerivAt_id' y).neg).mul_const s
      have h2 := h1.exp
      have h3 := (h2.mul_const (s ^ (α - 1 / 2))).mul_const ((1 + s ^ 2) ^ (-(β + 1 / 2)))
      have h4 := h3.const_mul (s ^ p * (s ^ 2 / (1 + s ^ 2)) ^ q)
      exact h4.congr_deriv (by ring)
  rw [integral_neg] at key
  unfold Bmom
  exact key

theorem iteratedDeriv_Bmom_gen (α β : ℝ) (hα : 0 ≤ α) (q : ℕ) (i : ℕ) :
    ∀ (p : ℕ) (y : ℝ), 0 < y →
      iteratedDeriv i (fun y => Bmom α β y p q) y = (-1) ^ i * Bmom α β y (p + i) q := by
  induction i with
  | zero =>
    intro p y _
    rw [iteratedDeriv_zero]
    simp
  | succ i ih =>
    intro p y hy
    have hev : iteratedDeriv i (fun y => Bmom α β y p q) =ᶠ[nhds y]
        (fun y => (-1 : ℝ) ^ i * Bmom α β y (p + i) q) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hy) (fun u hu => ih p u hu)
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := (hasDerivAt_Bmom α β hα (p + i) q y hy).const_mul ((-1 : ℝ) ^ i)
    rw [hd.deriv, ← add_assoc]
    ring

theorem iteratedDeriv_Bmom (α β : ℝ) (hα : 0 ≤ α) (i q : ℕ) (y : ℝ) (hy : 0 < y) :
    iteratedDeriv i (fun y => Bmom α β y 0 q) y = (-1) ^ i * Bmom α β y i q := by
  rw [iteratedDeriv_Bmom_gen α β hα q i 0 y hy, zero_add]

theorem Bmom_contDiffOn (α β : ℝ) (hα : 0 ≤ α) (p q : ℕ) :
    ContDiffOn ℝ ∞ (fun y => Bmom α β y p q) (Set.Ioi 0) := by
  apply contDiffOn_of_iter_differentiable _ isOpen_Ioi
  intro m x hx
  have hd := ((hasDerivAt_Bmom α β hα (p + m) q x hx).const_mul ((-1 : ℝ) ^ m)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx)
      (fun u hu => iteratedDeriv_Bmom_gen α β hα q m p u hu))
  exact hd.differentiableAt

end Painleve

