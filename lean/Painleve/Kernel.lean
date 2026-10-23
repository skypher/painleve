import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace Painleve

open MeasureTheory Set Filter Topology

/-- `x ↦ e^{-y x} x^K` is integrable on `(0,∞)` for `K > -1`. -/
lemma integrableOn_exp_rpow (K y : ℝ) (hK : -1 < K) (hy : 0 < y) :
    IntegrableOn (fun s : ℝ => Real.exp (-y * s) * s ^ K) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := K) (b := y) hK one_pos hy
  simp only [Real.rpow_one] at h
  exact h.congr_fun (fun x _ => by dsimp only; ring) measurableSet_Ioi

theorem integrableOn_kernel (y w α β : ℝ) (hy : 0 < y) (hw : 0 < w) (hα : 0 ≤ α) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.exp (-y * s) * s ^ (α - 1/2) * (1 + w * s ^ 2) ^ (-(β + 1/2)))
      (Set.Ioi 0) := by
  set a := α - 1/2 with ha_def
  set c := -(β + 1/2) with hc_def
  set N : ℝ := 2 * |c| with hN_def
  have ha : -1 < a := by rw [ha_def]; linarith
  have hN : 0 ≤ N := by rw [hN_def]; positivity
  have hpow : ∀ s : ℝ, 0 ≤ s → (1 + s) ^ N ≤ 2 ^ N * (1 + s ^ N) := by
    intro s hs
    have h1 : 1 + s ≤ 2 * max 1 s := by
      linarith [le_max_left 1 s, le_max_right 1 s]
    have h2 : (1 + s) ^ N ≤ (2 * max 1 s) ^ N :=
      Real.rpow_le_rpow (by linarith) h1 hN
    have h3 : (2 * max 1 s) ^ N = 2 ^ N * (max 1 s) ^ N :=
      Real.mul_rpow (by norm_num) (le_max_of_le_left zero_le_one)
    have h4 : (max 1 s) ^ N ≤ 1 + s ^ N := by
      have hsN := Real.rpow_nonneg hs N
      rcases le_total s 1 with h | h
      · rw [max_eq_left h, Real.one_rpow]; linarith
      · rw [max_eq_right h]; linarith
    calc (1 + s) ^ N ≤ (2 * max 1 s) ^ N := h2
      _ = 2 ^ N * (max 1 s) ^ N := h3
      _ ≤ 2 ^ N * (1 + s ^ N) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have hfac : ∀ s : ℝ, 0 < s → (1 + w * s ^ 2) ^ c ≤ (1 + w) ^ |c| * (1 + s) ^ N := by
    intro s hs
    have hB : 1 + w * s ^ 2 ≤ (1 + w) * (1 + s) ^ 2 := by
      nlinarith [mul_pos hw hs, sq_nonneg s, mul_nonneg hw.le (sq_nonneg s), hs]
    have hX1 : (1:ℝ) ≤ 1 + w * s ^ 2 := by nlinarith [mul_nonneg hw.le (sq_nonneg s)]
    rcases le_total 0 c with hc0 | hc0
    · rw [abs_of_nonneg hc0, hN_def, abs_of_nonneg hc0]
      have hsq : ((1 + s) ^ 2 : ℝ) ^ c = (1 + s) ^ (2 * c) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
      calc (1 + w * s ^ 2) ^ c ≤ ((1 + w) * (1 + s) ^ 2) ^ c :=
            Real.rpow_le_rpow (by linarith) hB hc0
        _ = (1 + w) ^ c * ((1 + s) ^ 2) ^ c :=
            Real.mul_rpow (by linarith) (by positivity)
        _ = (1 + w) ^ c * (1 + s) ^ (2 * c) := by rw [hsq]
    · have h1 : (1 + w * s ^ 2) ^ c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 hc0
      have h2 : (1:ℝ) ≤ (1 + w) ^ |c| := Real.one_le_rpow (by linarith) (abs_nonneg c)
      have h3 : (1:ℝ) ≤ (1 + s) ^ N := Real.one_le_rpow (by linarith) hN
      calc (1 + w * s ^ 2) ^ c ≤ 1 := h1
        _ ≤ (1 + w) ^ |c| * (1 + s) ^ N := one_le_mul_of_one_le_of_one_le h2 h3
  set K : ℝ := (1 + w) ^ |c| * 2 ^ N with hK_def
  have hK0 : 0 ≤ K := by rw [hK_def]; positivity
  have I1 : IntegrableOn (fun s : ℝ => Real.exp (-y * s) * s ^ a) (Set.Ioi 0) :=
    integrableOn_exp_rpow a y ha hy
  have I2 : IntegrableOn (fun s : ℝ => Real.exp (-y * s) * s ^ (a + N)) (Set.Ioi 0) :=
    integrableOn_exp_rpow (a + N) y (by linarith) hy
  have I := (I1.add I2).const_mul K
  refine Integrable.mono' I ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hE : 0 ≤ Real.exp (-y * s) * s ^ a := by positivity
    have hsplit : s ^ a * s ^ N = s ^ (a + N) := (Real.rpow_add hs0 a N).symm
    have hnn : 0 ≤ Real.exp (-y * s) * s ^ (a) * (1 + w * s ^ 2) ^ c := by
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + w * s ^ 2 by positivity) c
      positivity
    rw [Real.norm_of_nonneg hnn]
    calc Real.exp (-y * s) * s ^ a * (1 + w * s ^ 2) ^ c
        ≤ Real.exp (-y * s) * s ^ a * ((1 + w) ^ |c| * (1 + s) ^ N) :=
          mul_le_mul_of_nonneg_left (hfac s hs0) hE
      _ ≤ Real.exp (-y * s) * s ^ a * ((1 + w) ^ |c| * (2 ^ N * (1 + s ^ N))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hpow s hs0.le) (by positivity)) hE
      _ = K * (Real.exp (-y * s) * s ^ a + Real.exp (-y * s) * s ^ (a + N)) := by
          rw [hK_def, ← hsplit]; ring
      _ = (K * ((fun s : ℝ => Real.exp (-y * s) * s ^ a) s
            + (fun s : ℝ => Real.exp (-y * s) * s ^ (a + N)) s)) := rfl

/-- Derivative of `s ↦ s^(3/2) (1+w s^2)^(-1/2)`. -/
lemma hasDerivAt_F (w x : ℝ) (hw : 0 < w) (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
      ((1/2) * (x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
        + x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ))) x := by
  have hX : 0 < 1 + w * x ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ (3/2 : ℝ)) ((1:ℝ) * (3/2) * x ^ ((3/2 : ℝ) - 1)) x :=
    (hasDerivAt_id' x).rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun s : ℝ => 1 + w * s ^ 2) (w * ((2:ℕ) * x ^ (2 - 1))) x :=
    ((hasDerivAt_pow 2 x).const_mul w).const_add 1
  have h3 : HasDerivAt (fun s : ℝ => (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
      (w * ((2:ℕ) * x ^ (2 - 1)) * (-(1/2)) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ) - 1)) x :=
    h2.rpow_const (Or.inl hX.ne')
  have h := h1.mul h3
  refine h.congr_deriv ?_
  have hs32 : x ^ (3/2 : ℝ) = x ^ (1/2 : ℝ) * x := by
    rw [show (3/2 : ℝ) = 1/2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
  have hB : (1 + w * x ^ 2) ^ (-(3/2 : ℝ)) * (1 + w * x ^ 2) = (1 + w * x ^ 2) ^ (-(1/2 : ℝ)) := by
    have h' := Real.rpow_add hX (-(3/2 : ℝ)) 1
    rw [Real.rpow_one, show (-(3/2 : ℝ)) + 1 = -(1/2 : ℝ) by norm_num] at h'
    exact h'.symm
  rw [hs32, show (3/2 : ℝ) - 1 = 1/2 by norm_num, show (-(1/2 : ℝ)) - 1 = -(3/2 : ℝ) by norm_num]
  norm_num
  linear_combination (-(x ^ (1/2 : ℝ))) * hB

theorem ibp_kernel (y w : ℝ) (hy : 0 < y) (hw : 0 < w) :
    y * ∫ s in Set.Ioi (0:ℝ), Real.exp (-y * s) * s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)) =
      (1/2) * (∫ s in Set.Ioi (0:ℝ), Real.exp (-y * s) * s ^ (1/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ))) +
      ∫ s in Set.Ioi (0:ℝ), Real.exp (-y * s) * s ^ (1/2 : ℝ) * (1 + w * s ^ 2) ^ (-(3/2 : ℝ)) := by
  have k1 : IntegrableOn
      (fun s : ℝ => Real.exp (-y * s) * s ^ (1/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
      (Set.Ioi 0) :=
    (integrableOn_kernel y w 1 0 hy hw zero_le_one).congr_fun (fun s _ => by norm_num)
      measurableSet_Ioi
  have k2 : IntegrableOn
      (fun s : ℝ => Real.exp (-y * s) * s ^ (1/2 : ℝ) * (1 + w * s ^ 2) ^ (-(3/2 : ℝ)))
      (Set.Ioi 0) :=
    (integrableOn_kernel y w 1 1 hy hw zero_le_one).congr_fun (fun s _ => by norm_num)
      measurableSet_Ioi
  have k3 : IntegrableOn
      (fun s : ℝ => Real.exp (-y * s) * s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
      (Set.Ioi 0) :=
    (integrableOn_kernel y w 2 0 hy hw (by norm_num)).congr_fun (fun s _ => by norm_num)
      measurableSet_Ioi
  -- the functions of the integration by parts
  have hd_u : ∀ x : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-y * s)) (-y * Real.exp (-y * x)) x := by
    intro x
    refine (((hasDerivAt_id' x).const_mul (-y)).exp).congr_deriv ?_
    ring
  have hd_v : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun s : ℝ => s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
        ((fun x : ℝ => (1/2) * (x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
          + x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ))) x) x :=
    fun x hx => hasDerivAt_F w x hw hx
  have hint_uv : IntegrableOn
      ((fun s : ℝ => Real.exp (-y * s)) *
        (fun x : ℝ => (1/2) * (x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
          + x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ))))
      (Set.Ioi 0) :=
    IntegrableOn.congr_fun ((k1.const_mul (1/2 : ℝ)).add k2) (fun x _ => by
      simp only [Pi.mul_apply, Pi.add_apply]; ring) measurableSet_Ioi
  have hint_u'v : IntegrableOn
      ((fun s : ℝ => -y * Real.exp (-y * s)) *
        (fun s : ℝ => s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ))))
      (Set.Ioi 0) :=
    IntegrableOn.congr_fun (k3.const_mul (-y)) (fun x _ => by
      simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have h_zero : Tendsto
      ((fun s : ℝ => Real.exp (-y * s)) *
        (fun s : ℝ => s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun s : ℝ => Real.exp (-y * s) * (s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))) 0 := by
      apply ContinuousAt.mul
      · fun_prop
      · apply ContinuousAt.mul
        · exact Real.continuousAt_rpow_const 0 (3/2) (Or.inr (by norm_num))
        · exact ContinuousAt.rpow_const (by fun_prop) (Or.inl (by norm_num))
    have h0 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    have hval : Real.exp (-y * 0) * ((0:ℝ) ^ (3/2 : ℝ) * (1 + w * 0 ^ 2) ^ (-(1/2 : ℝ))) = 0 := by
      rw [Real.zero_rpow (by norm_num)]; simp
    rw [hval] at h0
    exact h0
  have h_infty : Tendsto
      ((fun s : ℝ => Real.exp (-y * s)) *
        (fun s : ℝ => s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ))))
      atTop (𝓝 0) := by
    have hg : Tendsto (fun t : ℝ => Real.exp (-y * t) * t ^ (3/2 : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3/2) y hy).congr (fun t => by ring)
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_ge_atTop 0] with t ht
      show 0 ≤ Real.exp (-y * t) * (t ^ (3/2 : ℝ) * (1 + w * t ^ 2) ^ (-(1/2 : ℝ)))
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.rpow_nonneg ht _)
        (Real.rpow_nonneg (by nlinarith [mul_nonneg hw.le (sq_nonneg t)]) _))
    · filter_upwards [eventually_ge_atTop 0] with t ht
      show Real.exp (-y * t) * (t ^ (3/2 : ℝ) * (1 + w * t ^ 2) ^ (-(1/2 : ℝ)))
        ≤ Real.exp (-y * t) * t ^ (3/2 : ℝ)
      have hg1 : (1 + w * t ^ 2) ^ (-(1/2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [mul_nonneg hw.le (sq_nonneg t)])
          (by norm_num)
      have hp : 0 ≤ t ^ (3/2 : ℝ) := Real.rpow_nonneg ht _
      have he : 0 ≤ Real.exp (-y * t) := (Real.exp_pos _).le
      calc Real.exp (-y * t) * (t ^ (3/2 : ℝ) * (1 + w * t ^ 2) ^ (-(1/2 : ℝ)))
          ≤ Real.exp (-y * t) * (t ^ (3/2 : ℝ) * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg1 hp) he
        _ = Real.exp (-y * t) * t ^ (3/2 : ℝ) := by ring
  have hIBP := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun s : ℝ => Real.exp (-y * s))
    (v := fun s : ℝ => s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
    (u' := fun s : ℝ => -y * Real.exp (-y * s))
    (v' := fun x : ℝ => (1/2) * (x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
          + x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ)))
    (fun x _ => hd_u x) hd_v hint_uv hint_u'v h_zero h_infty
  have e1 : ∫ x in Set.Ioi (0:ℝ), Real.exp (-y * x) * ((1/2) * (x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
          + x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ)))
      = (1/2) * (∫ s in Set.Ioi (0:ℝ), Real.exp (-y * s) * s ^ (1/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)))
        + ∫ s in Set.Ioi (0:ℝ), Real.exp (-y * s) * s ^ (1/2 : ℝ) * (1 + w * s ^ 2) ^ (-(3/2 : ℝ)) := by
    have hfun : (fun x : ℝ => Real.exp (-y * x) * ((1/2) * (x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
          + x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ))))
        = fun x : ℝ => (1/2) * (Real.exp (-y * x) * x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
          + Real.exp (-y * x) * x ^ (1/2 : ℝ) * (1 + w * x ^ 2) ^ (-(3/2 : ℝ)) := by
      funext x; ring
    rw [hfun, integral_add (k1.const_mul (1/2 : ℝ)) k2, integral_const_mul]
  have e2 : ∫ x in Set.Ioi (0:ℝ), (-y * Real.exp (-y * x)) * (x ^ (3/2 : ℝ) * (1 + w * x ^ 2) ^ (-(1/2 : ℝ)))
      = -y * ∫ s in Set.Ioi (0:ℝ), Real.exp (-y * s) * s ^ (3/2 : ℝ) * (1 + w * s ^ 2) ^ (-(1/2 : ℝ)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  beta_reduce at hIBP
  linarith [hIBP, e1, e2]

end Painleve
