import Painleve.PlanarOde
import Painleve.Weighted
import Painleve.HSeries
import Painleve.OdeUnique
import Painleve.PhiHankel
import Painleve.Phi
import Painleve.Ibp
import Painleve.Statement
import Painleve.Calc

namespace Painleve
open Complex Filter MeasureTheory
open scoped ComplexConjugate ContDiff Topology

lemma mom_eq_wsrc (k : ℕ) (a : ℝ) : mom a k k = wsrc k a 1 := by
  have h1 : ∀ z : ℂ, z ^ k * conj z ^ k = ((‖z‖ ^ (2 * k) : ℝ) : ℂ) := by
    intro z
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow, ← pow_mul]
  unfold mom wsrc
  congr 1
  funext z
  rw [h1]
  simp [density]

lemma iter_hPlanar_eq (k : ℕ) (a : ℝ) (ha : 0 < a) :
    iteratedDeriv k hPlanar a = (-1 : ℂ) ^ k * wsrc k a 1 := by
  rw [iteratedDeriv_hPlanar k a ha, mom_eq_wsrc]

lemma hPlanar_iter_diff (k : ℕ) (a0 : ℝ) (ha0 : 0 < a0) :
    DifferentiableAt ℝ (iteratedDeriv k hPlanar) a0 := by
  have hd := (hasDerivAt_wsrc k a0 1 ha0).const_mul ((-1 : ℂ) ^ k)
  have hev : iteratedDeriv k hPlanar =ᶠ[𝓝 a0] (fun a => (-1 : ℂ) ^ k * wsrc k a 1) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ha0) (fun a ha => iter_hPlanar_eq k a ha)
  exact (hd.congr_of_eventuallyEq hev).differentiableAt

lemma hPlanar_contDiffOn : ContDiffOn ℝ ∞ hPlanar (Set.Ioi 0) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m _ x hx
  have hd : DifferentiableAt ℝ (iteratedDeriv m hPlanar) x := hPlanar_iter_diff m x hx
  exact (hd.differentiableWithinAt).congr
    (fun y hy => iteratedDerivWithin_of_isOpen isOpen_Ioi hy)
    (iteratedDerivWithin_of_isOpen isOpen_Ioi hx)

lemma hPlanar_differentiableAt (a : ℝ) (ha : 0 < a) : DifferentiableAt ℝ hPlanar a := by
  have h := hPlanar_iter_diff 0 a ha
  rwa [iteratedDeriv_zero] at h

lemma iter_sub_gen (f g : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0))
    (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) (n : ℕ) :
    ∀ x ∈ Set.Ioi (0 : ℝ), iteratedDeriv n (fun t => f t - g t) x
      = iteratedDeriv n f x - iteratedDeriv n g x := by
  induction n with
  | zero => intro x _; simp [iteratedDeriv_zero]
  | succ n ih =>
    intro x hx
    have hev : iteratedDeriv n (fun t => f t - g t)
        =ᶠ[𝓝 x] (fun t => iteratedDeriv n f t - iteratedDeriv n g t) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) (fun y hy => ih y hy)
    simp only [iteratedDeriv_succ]
    rw [hev.deriv_eq]
    apply deriv_sub
    · exact ((iter_smooth f hf n).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)
    · exact ((iter_smooth g hg n).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)

lemma hPlanar_eq_Phi0 (a : ℝ) (ha : 0 < a) :
    hPlanar a = ((Real.sqrt (Real.pi / 2) * Phi 0 0 (a ^ 2 / 2) 1 : ℝ) : ℂ) := by
  have h := iter_hPlanar_eq 0 a ha
  rw [iteratedDeriv_zero, pow_zero, one_mul] at h
  rw [h, wsrc_zero a 1 ha one_pos, one_pow]

lemma deriv_hPlanar_eq (a : ℝ) (ha : 0 < a) :
    deriv hPlanar a = ((-(a * Real.sqrt (Real.pi / 2) * Phi 1 0 (a ^ 2 / 2) 1) : ℝ) : ℂ) := by
  rw [← iteratedDeriv_one, iter_hPlanar_eq 1 a ha, wsrc_one a 1 ha one_pos, one_pow]
  push_cast
  ring

lemma iter2_hPlanar_eq (a : ℝ) (ha : 0 < a) :
    iteratedDeriv 2 hPlanar a = ((2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (a ^ 2 / 2) 1 : ℝ) : ℂ) := by
  rw [iter_hPlanar_eq 2 a ha, wsrc_two a 1 ha one_pos, one_pow]
  push_cast
  ring

lemma hasDerivAt_hSeries (a : ℝ) : HasDerivAt hSeries (deriv hSeries a) a :=
  ((hSeries_contDiff.differentiable (by simp)) a).hasDerivAt

lemma hS_ofReal_contDiffOn :
    ContDiffOn ℝ ∞ (fun t : ℝ => ((hSeries t : ℝ) : ℂ)) (Set.Ioi 0) :=
  (Complex.ofRealCLM.contDiff.comp hSeries_contDiff).contDiffOn

lemma W_contDiffOn :
    ContDiffOn ℝ ∞ (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) (Set.Ioi 0) :=
  hPlanar_contDiffOn.sub hS_ofReal_contDiffOn

lemma hode_W (a : ℝ) (ha : 0 < a) :
    iteratedDeriv 3 (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) a
      + (a : ℂ) ^ 2 * deriv (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) a
      + (a : ℂ) * (hPlanar a - ((hSeries a : ℝ) : ℂ)) = 0 := by
  have e := iter_sub_gen hPlanar (fun t => ((hSeries t : ℝ) : ℂ)) hPlanar_contDiffOn
    hS_ofReal_contDiffOn 3 a ha
  have e2 := iteratedDeriv_ofReal_comm hSeries isOpen_Ioi hSeries_contDiff.contDiffOn 3 a ha
  rw [e2] at e
  have h3 : iteratedDeriv 3 (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) a
      = iteratedDeriv 3 hPlanar a - ((iteratedDeriv 3 hSeries a : ℝ) : ℂ) := e
  have hd : deriv (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) a
      = deriv hPlanar a - ((deriv hSeries a : ℝ) : ℂ) := by
    have hHS : HasDerivAt (fun t => ((hSeries t : ℝ) : ℂ)) ((deriv hSeries a : ℝ) : ℂ) a :=
      (hasDerivAt_hSeries a).ofReal_comp
    exact ((hPlanar_differentiableAt a ha).hasDerivAt.sub hHS).deriv
  rw [h3, hd]
  have hP := hPlanar_ode a ha
  have hS' := congrArg (fun x : ℝ => (x : ℂ)) (hSeries_ode a)
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_zero] at hS'
  linear_combination hP - hS'

theorem hPlanar_eq_hBessel
    (hL0 : Tendsto (fun a : ℝ => Phi 0 0 (a ^ 2 / 2) 1) (𝓝[>] 0)
      (𝓝 (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi))))
    (hL1 : Tendsto (fun a : ℝ => a * Phi 1 0 (a ^ 2 / 2) 1) (𝓝[>] 0) (𝓝 (Real.sqrt (2 * Real.pi))))
    (hL2 : Tendsto (fun a : ℝ => Phi 1 1 (a ^ 2 / 2) 1) (𝓝[>] 0)
      (𝓝 (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi)))
    (hg0 : Real.sqrt (Real.pi / 2) * (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)) =
      Real.pi ^ 2 * Real.sqrt 8 / (4 * Real.Gamma (3 / 4) ^ 2))
    (hg1 : -(Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi)) =
      -(Real.pi ^ 2 * Real.sqrt 2 / (4 * (Real.Gamma (3 / 4) * Real.Gamma (5 / 4)))))
    (hg2 : 2 * Real.sqrt (Real.pi / 2) * (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi) =
      Real.pi ^ 2 / (2 * Real.sqrt 8 * Real.Gamma (5 / 4) ^ 2))
    (a : ℝ) (ha : 0 < a) :
    hPlanar a = ((hBessel a : ℝ) : ℂ) := by
  -- value at 0⁺
  have hW0 : Tendsto (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hA : Tendsto (fun t => hPlanar t) (𝓝[>] 0)
        (𝓝 (((Real.sqrt (Real.pi / 2) * (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)) : ℝ)) : ℂ)) := by
      have h := (Complex.continuous_ofReal.tendsto _).comp
        (hL0.const_mul (Real.sqrt (Real.pi / 2)))
      exact h.congr' (eventually_nhdsWithin_of_forall (fun t ht => (hPlanar_eq_Phi0 t ht).symm))
    have hB : Tendsto (fun t => ((hSeries t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (((hSeries 0 : ℝ)) : ℂ)) :=
      ((Complex.continuous_ofReal.comp hSeries_contDiff.continuous).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hval : ((Real.sqrt (Real.pi / 2) * (Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)) : ℝ) : ℂ)
        - ((hSeries 0 : ℝ) : ℂ) = 0 := by
      rw [hg0, hSeries_zero, sub_self]
    have h := hA.sub hB
    rw [hval] at h
    exact h
  -- derivative at 0⁺
  have hW1 : Tendsto (deriv (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    have hEq : ∀ t : ℝ, 0 < t → deriv (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) t
        = ((-(t * Real.sqrt (Real.pi / 2) * Phi 1 0 (t ^ 2 / 2) 1) : ℝ) : ℂ)
          - ((deriv hSeries t : ℝ) : ℂ) := by
      intro t ht
      have hHS : HasDerivAt (fun t => ((hSeries t : ℝ) : ℂ)) ((deriv hSeries t : ℝ) : ℂ) t :=
        (hasDerivAt_hSeries t).ofReal_comp
      have hd : HasDerivAt (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ))
          (deriv hPlanar t - ((deriv hSeries t : ℝ) : ℂ)) t :=
        (hPlanar_differentiableAt t ht).hasDerivAt.sub hHS
      rw [hd.deriv, deriv_hPlanar_eq t ht]
    have hA : Tendsto (fun t : ℝ => ((-(t * Real.sqrt (Real.pi / 2) * Phi 1 0 (t ^ 2 / 2) 1) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (((-(Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi))) : ℝ) : ℂ)) := by
      have h1 : Tendsto (fun t : ℝ => -(Real.sqrt (Real.pi / 2) * (t * Phi 1 0 (t ^ 2 / 2) 1)))
          (𝓝[>] 0) (𝓝 (-(Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi)))) :=
        (hL1.const_mul (Real.sqrt (Real.pi / 2))).neg
      have h2 : Tendsto (fun t : ℝ => -(t * Real.sqrt (Real.pi / 2) * Phi 1 0 (t ^ 2 / 2) 1))
          (𝓝[>] 0) (𝓝 (-(Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi)))) :=
        h1.congr (fun t => by ring)
      exact (Complex.continuous_ofReal.tendsto _).comp h2
    have hB : Tendsto (fun t => ((deriv hSeries t : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 (((deriv hSeries 0 : ℝ)) : ℂ)) :=
      ((Complex.continuous_ofReal.comp (hSeries_contDiff.continuous_deriv (by simp))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hval : ((-(Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi)) : ℝ) : ℂ)
        - ((deriv hSeries 0 : ℝ) : ℂ) = 0 := by
      rw [deriv_hSeries_zero, hg1, sub_self]
    have h := hA.sub hB
    rw [hval] at h
    exact h.congr' (eventually_nhdsWithin_of_forall (fun t ht => (hEq t ht).symm))
  -- second derivative at 0⁺
  have hW2 : Tendsto (iteratedDeriv 2 (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    have hEq : ∀ t : ℝ, 0 < t → iteratedDeriv 2 (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) t
        = ((2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (t ^ 2 / 2) 1 : ℝ) : ℂ)
          - ((iteratedDeriv 2 hSeries t : ℝ) : ℂ) := by
      intro t ht
      rw [iter_sub_gen hPlanar (fun t => ((hSeries t : ℝ) : ℂ)) hPlanar_contDiffOn
        hS_ofReal_contDiffOn 2 t ht, iter2_hPlanar_eq t ht,
        iteratedDeriv_ofReal_comm hSeries isOpen_Ioi hSeries_contDiff.contDiffOn 2 t ht]
    have hA : Tendsto (fun t : ℝ => ((2 * Real.sqrt (Real.pi / 2) * Phi 1 1 (t ^ 2 / 2) 1 : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (((2 * Real.sqrt (Real.pi / 2) * (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi)) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hL2.const_mul (2 * Real.sqrt (Real.pi / 2)))
    have hB : Tendsto (fun t => ((iteratedDeriv 2 hSeries t : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 (((iteratedDeriv 2 hSeries 0 : ℝ)) : ℂ)) :=
      ((Complex.continuous_ofReal.comp
        (hSeries_contDiff.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr (by simp)))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hval : ((2 * Real.sqrt (Real.pi / 2) * (Real.Gamma (3 / 4) ^ 2 / Real.sqrt Real.pi) : ℝ) : ℂ)
        - ((iteratedDeriv 2 hSeries 0 : ℝ) : ℂ) = 0 := by
      rw [iteratedDeriv_two_hSeries_zero, hg2, sub_self]
    have h := hA.sub hB
    rw [hval] at h
    exact h.congr' (eventually_nhdsWithin_of_forall (fun t ht => (hEq t ht).symm))
  -- ODE uniqueness
  have hW := ode3_unique (fun t => hPlanar t - ((hSeries t : ℝ) : ℂ)) W_contDiffOn
    (fun t ht => hode_W t ht) hW0 hW1 hW2 a ha
  have h : hPlanar a - ((hSeries a : ℝ) : ℂ) = 0 := hW
  rw [hBessel_eq_hSeries a ha]
  exact sub_eq_zero.mp h

end Painleve
