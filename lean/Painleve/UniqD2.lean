import Painleve.UniqD1
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The approximate solution (Section 8 of `paper.tex`)

`q(t) > 0` is the root of `q + (d-1) q^{d-1} = ε t`; it is smooth and increasing.
With `f = log q`: `f' = ε/(q + (d-1)² q^{d-1})`, so `0 < f'(t) ≤ 1/t`, and
`f'' = -f'² (1 + (d-1)³ q^{d-2})/(1 + (d-1)² q^{d-2})`, so `|f''(t)| ≤ (d-1)/t²`.
-/

open Set Filter Topology

namespace Painleve

variable {d : ℕ}

/-- `g(x) = x + (d-1) (max x 0)^{d-1}`: strictly increasing and onto `ℝ`. -/
noncomputable def gfun (d : ℕ) (x : ℝ) : ℝ := x + ((d - 1 : ℕ) : ℝ) * (max x 0) ^ (d - 1)

lemma gfun_strictMono : StrictMono (gfun d) := by
  intro x y hxy
  unfold gfun
  have h1 : (max x 0) ^ (d - 1) ≤ (max y 0) ^ (d - 1) :=
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max hxy.le le_rfl) _
  have h2 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

lemma gfun_continuous : Continuous (gfun d) := by unfold gfun; fun_prop

lemma gfun_surjective : Function.Surjective (gfun d) := by
  refine gfun_continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun x => ?_) tendsto_id
    unfold gfun
    have : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * (max x 0) ^ (d - 1) := by positivity
    simp only [id]; linarith
  · refine tendsto_id.congr' ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    unfold gfun
    rw [max_eq_right hx.le]
    rcases Nat.eq_zero_or_pos (d - 1) with h | h
    · rw [h, Nat.cast_zero, zero_mul, add_zero]; rfl
    · rw [zero_pow h.ne', mul_zero, add_zero]; rfl

/-- The order isomorphism `g`. -/
noncomputable def gIso (d : ℕ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (gfun d) gfun_strictMono gfun_surjective

/-- The approximate solution: `q(t) + (d-1) q(t)^{d-1} = ε t`. -/
noncomputable def qapp (d : ℕ) (ε t : ℝ) : ℝ := (gIso d).symm (ε * t)

lemma gfun_qapp (ε t : ℝ) : gfun d (qapp d ε t) = ε * t := by
  unfold qapp
  have := (gIso d).apply_symm_apply (ε * t)
  rwa [gIso, StrictMono.coe_orderIsoOfSurjective] at this

lemma qapp_pos {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) : 0 < qapp d ε t := by
  by_contra h
  push Not at h
  have h1 : gfun d (qapp d ε t) ≤ gfun d 0 := gfun_strictMono.monotone h
  rw [gfun_qapp] at h1
  have h0 : gfun d 0 = 0 := by
    unfold gfun; rw [max_self]
    rcases Nat.eq_zero_or_pos (d - 1) with h | h
    · rw [h, Nat.cast_zero, zero_mul, add_zero]
    · rw [zero_pow h.ne', mul_zero, add_zero]
  rw [h0] at h1
  have := mul_pos hε ht
  linarith

/-- `q + (d-1) q^{d-1} = ε t`. -/
lemma qapp_eq (hd : 1 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    qapp d ε t + ((d : ℝ) - 1) * qapp d ε t ^ (d - 1) = ε * t := by
  have h := gfun_qapp (d := d) ε t
  unfold gfun at h
  rw [max_eq_left (qapp_pos hε ht).le, Nat.cast_sub hd, Nat.cast_one] at h
  exact h

lemma qapp_mono {ε : ℝ} (hε : 0 < ε) : Monotone (qapp d ε) := by
  intro s t hst
  unfold qapp
  exact (gIso d).symm.monotone (mul_le_mul_of_nonneg_left hst hε.le)

/-- The polynomial `G(x) = x + (d-1) x^{d-1}` and its derivative. -/
noncomputable def Gpoly (d : ℕ) (x : ℝ) : ℝ := x + ((d - 1 : ℕ) : ℝ) * x ^ (d - 1)

noncomputable def Gder (d : ℕ) (x : ℝ) : ℝ := 1 + ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) * x ^ (d - 1 - 1))

lemma hasDerivAt_Gpoly (x : ℝ) : HasDerivAt (Gpoly d) (Gder d x) x := by
  unfold Gpoly Gder
  exact (hasDerivAt_id x).add ((hasDerivAt_pow (d - 1) x).const_mul _)

lemma Gder_pos {x : ℝ} (hx : 0 ≤ x) : 0 < Gder d x := by
  unfold Gder; positivity

lemma gfun_eq_Gpoly {x : ℝ} (hx : 0 < x) : gfun d =ᶠ[𝓝 x] Gpoly d := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  unfold gfun Gpoly; rw [max_eq_left (le_of_lt hy)]

/-- `q'(t) = ε / G'(q(t))`. -/
theorem hasDerivAt_qapp {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    HasDerivAt (qapp d ε) (ε / Gder d (qapp d ε t)) t := by
  have hq := qapp_pos (d := d) hε ht
  have hcont : ContinuousAt (gIso d).symm (ε * t) := (gIso d).symm.continuous.continuousAt
  have hG : HasDerivAt (gfun d) (Gder d ((gIso d).symm (ε * t))) ((gIso d).symm (ε * t)) := by
    have := hasDerivAt_Gpoly (d := d) ((gIso d).symm (ε * t))
    exact this.congr_of_eventuallyEq (gfun_eq_Gpoly hq)
  have hinv := HasDerivAt.of_local_left_inverse hcont hG (Gder_pos hq.le).ne'
    (Eventually.of_forall fun y => by
      have := (gIso d).apply_symm_apply y
      rwa [gIso, StrictMono.coe_orderIsoOfSurjective] at this)
  have hlin : HasDerivAt (fun s : ℝ => ε * s) ε t := by
    simpa using (hasDerivAt_id t).const_mul ε
  have := hinv.comp t hlin
  unfold qapp
  refine this.congr_deriv ?_
  rw [inv_mul_eq_div]

/-- `f' = ε/(q + (d-1)² q^{d-1})`, the derivative of `log q`. -/
noncomputable def fp (d : ℕ) (ε t : ℝ) : ℝ := ε / (qapp d ε t * Gder d (qapp d ε t))

theorem hasDerivAt_logq {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (qapp d ε s)) (fp d ε t) t := by
  have hq := qapp_pos (d := d) hε ht
  refine ((hasDerivAt_qapp hε ht).log hq.ne').congr_deriv ?_
  unfold fp
  field_simp

/-- `H(y) = y G'(y) = y + (d-1)² y^{d-1}`, so that `f' = ε/H(q)`. -/
noncomputable def Hpoly (d : ℕ) (y : ℝ) : ℝ := y + ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) * y ^ (d - 1))

noncomputable def Hder (d : ℕ) (y : ℝ) : ℝ :=
  1 + ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) * ((d - 1 : ℕ) * y ^ (d - 1 - 1)))

lemma hasDerivAt_Hpoly (y : ℝ) : HasDerivAt (Hpoly d) (Hder d y) y := by
  unfold Hpoly Hder
  exact (hasDerivAt_id y).add (((hasDerivAt_pow (d - 1) y).const_mul _).const_mul _)

lemma mul_Gder (hd : 2 ≤ d) (y : ℝ) : y * Gder d y = Hpoly d y := by
  unfold Gder Hpoly
  have : y * y ^ (d - 1 - 1) = y ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
  linear_combination (((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ)) * this

lemma fp_eq (hd : 2 ≤ d) (ε t : ℝ) : fp d ε t = ε / Hpoly d (qapp d ε t) := by
  unfold fp; rw [mul_Gder hd]

lemma Hpoly_pos {y : ℝ} (hy : 0 < y) : 0 < Hpoly d y := by unfold Hpoly; positivity

lemma Hder_pos {y : ℝ} (hy : 0 ≤ y) : 0 < Hder d y := by unfold Hder; positivity

/-- `0 < f'(t) ≤ 1/t`. -/
theorem fp_bounds (hd : 2 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    0 < fp d ε t ∧ fp d ε t ≤ 1 / t := by
  have hq := qapp_pos (d := d) hε ht
  have heq := qapp_eq (d := d) (by omega) hε ht
  rw [fp_eq hd]
  have hH := Hpoly_pos (d := d) hq
  refine ⟨div_pos hε hH, ?_⟩
  rw [div_le_div_iff₀ hH ht, one_mul]
  -- `ε t = q + (d-1) q^{d-1} ≤ H(q)`
  unfold Hpoly
  have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hc]
  have h1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h2 : 0 ≤ ((d : ℝ) - 1) * qapp d ε t ^ (d - 1) := by positivity
  nlinarith

/-- `f''`. -/
noncomputable def fpp (d : ℕ) (ε t : ℝ) : ℝ :=
  -(ε * Hder d (qapp d ε t) * (ε / Gder d (qapp d ε t))) / Hpoly d (qapp d ε t) ^ 2

theorem hasDerivAt_fp (hd : 2 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    HasDerivAt (fp d ε) (fpp d ε t) t := by
  have hq := qapp_pos (d := d) hε ht
  have hH := Hpoly_pos (d := d) hq
  have h1 : HasDerivAt (fun s => Hpoly d (qapp d ε s)) (Hder d (qapp d ε t) * (ε / Gder d (qapp d ε t))) t :=
    (hasDerivAt_Hpoly (qapp d ε t)).comp t (hasDerivAt_qapp hε ht)
  have h2 := h1.inv hH.ne'
  have h3 := h2.const_mul ε
  have hfun : fp d ε = fun s => ε * (Hpoly d (qapp d ε s))⁻¹ := by
    funext s; rw [fp_eq hd, div_eq_mul_inv]
  rw [hfun]
  refine h3.congr_deriv ?_
  unfold fpp
  field_simp

/-- `|f''(t)| ≤ (d-1) f'(t)²`. -/
theorem fpp_bound (hd : 2 ≤ d) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    |fpp d ε t| ≤ ((d : ℝ) - 1) * fp d ε t ^ 2 := by
  have hq := qapp_pos (d := d) hε ht
  set y := qapp d ε t with hy
  have hH := Hpoly_pos (d := d) hq
  have hG := Gder_pos (d := d) hq.le
  have hHd := Hder_pos (d := d) hq.le
  have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have h1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- `|f''| = f'² · y H'(y)/H(y)` and `y H'(y) ≤ (d-1) H(y)`
  have hyHd : y * Hder d y ≤ ((d : ℝ) - 1) * Hpoly d y := by
    unfold Hder Hpoly
    rw [hc]
    have e : y * y ^ (d - 1 - 1) = y ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    have hp : 0 ≤ y ^ (d - 1) := by positivity
    calc y * (1 + ((d : ℝ) - 1) * (((d : ℝ) - 1) * (((d : ℝ) - 1) * y ^ (d - 1 - 1))))
        = y + ((d : ℝ) - 1) ^ 3 * (y * y ^ (d - 1 - 1)) := by ring
      _ = y + ((d : ℝ) - 1) ^ 3 * y ^ (d - 1) := by rw [e]
      _ ≤ ((d : ℝ) - 1) * (y + ((d : ℝ) - 1) * (((d : ℝ) - 1) * y ^ (d - 1))) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1 - 1) hq.le]
  have hfpp : fpp d ε t = -(fp d ε t ^ 2 * (y * Hder d y / Hpoly d y)) := by
    unfold fpp; rw [fp_eq hd, ← hy, ← mul_Gder hd]
    field_simp
  rw [hfpp, abs_neg, abs_of_nonneg (by positivity)]
  have : y * Hder d y / Hpoly d y ≤ (d : ℝ) - 1 := by rw [div_le_iff₀ hH]; exact hyHd
  have hfp2 : 0 ≤ fp d ε t ^ 2 := sq_nonneg _
  nlinarith

/-- **Second-order Taylor bound** on `[0, 1]`. -/
theorem taylor2 {g g' g'' : ℝ → ℝ} {M : ℝ} (hg : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g' (g'' x) x) (hM : ∀ x ∈ Icc (0 : ℝ) 1, |g'' x| ≤ M) :
    |g 1 - g 0 - g' 0| ≤ M / 2 := by
  have hstep1 : ∀ x ∈ Icc (0 : ℝ) 1, ‖g' x - g' 0‖ ≤ M * (x - 0) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment
      (fun x hx => (hg' x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg' x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hM x (Ico_subset_Icc_self hx))
  have hB : ∀ x, HasDerivAt (fun x : ℝ => M * x ^ 2 / 2) (M * x) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_mul M).div_const 2
    refine this.congr_deriv ?_
    push_cast; ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun x => g x - g 0 - x * g' 0) (f' := fun x => g' x - g' 0) (a := 0) (b := 1)
    (fun x hx => (((hg x hx).sub_const _).sub ((hasDerivAt_id x).mul_const _)).continuousAt.continuousWithinAt)
    (fun x hx => by
      have := ((hg x (Ico_subset_Icc_self hx)).sub_const (g 0)).sub ((hasDerivAt_id x).mul_const (g' 0))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp)
    (by simp) hB
    (fun x hx => by
      have := hstep1 x (Ico_subset_Icc_self hx)
      simpa using this)
    (right_mem_Icc.mpr zero_le_one)
  simp only [one_mul, Real.norm_eq_abs, one_pow, mul_one] at h
  exact h

end Painleve
