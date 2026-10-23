import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Painleve
open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable def diskSource (a R : ℝ) (r : ℕ) (u v : ℂ) : ℂ :=
  ∫ z in Metric.closedBall (0 : ℂ) R, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (u * z ^ 4 + v * conj z ^ 4))

/-- Integrand of `diskSource` with the sources replaced by `u * exp s`, `v * exp (-s)`. -/
noncomputable def diskFun (a : ℝ) (r : ℕ) (u v s z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
    (I / 4) * (u * Complex.exp s * z ^ 4 + v * Complex.exp (-s) * conj z ^ 4))

/-- Its derivative in `s`. -/
noncomputable def diskDer (a : ℝ) (r : ℕ) (u v s z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * (Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
    (I / 4) * (u * Complex.exp s * z ^ 4 + v * Complex.exp (-s) * conj z ^ 4)) *
    ((I / 4) * (u * Complex.exp s * z ^ 4 - v * Complex.exp (-s) * conj z ^ 4)))

/-- `s ↦ diskSource` along the exponential parametrisation of the sources. -/
noncomputable def diskH (a R : ℝ) (r : ℕ) (u v : ℂ) (s : ℂ) : ℂ :=
  diskSource a R r (u * Complex.exp s) (v * Complex.exp (-s))

/-- Integration over the closed ball is invariant under a rotation of the ball. -/
lemma setIntegral_rot_ball (R : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (g : ℂ → ℂ) :
    ∫ z in Metric.closedBall (0 : ℂ) R, g (ζ * z) = ∫ z in Metric.closedBall (0 : ℂ) R, g z := by
  let w : Circle := ⟨ζ, mem_sphere_zero_iff_norm.2 hζ⟩
  have hw : ((w : Circle) : ℂ) = ζ := rfl
  have hmp : MeasurePreserving (rotation w) volume volume := (rotation w).measurePreserving
  have hemb : MeasurableEmbedding (rotation w) := (rotation w).toHomeomorph.measurableEmbedding
  have hpre : rotation w ⁻¹' Metric.closedBall (0 : ℂ) R = Metric.closedBall (0 : ℂ) R := by
    ext z
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, rotation_apply, hw, norm_mul, hζ, one_mul]
  have := hmp.setIntegral_preimage_emb hemb g (Metric.closedBall (0 : ℂ) R)
  rw [hpre] at this
  simpa [rotation_apply, hw] using this

lemma setIntegral_ball_rot_eq (R : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (g h : ℂ → ℂ)
    (hgh : ∀ z, g (ζ * z) = h z) :
    ∫ z in Metric.closedBall (0 : ℂ) R, g z = ∫ z in Metric.closedBall (0 : ℂ) R, h z := by
  rw [← setIntegral_rot_ball R ζ hζ g]
  congr 1
  funext z
  exact hgh z

theorem diskSource_rotate (a R : ℝ) (r : ℕ) (u v : ℂ) (φ : ℝ) :
    diskSource a R r (u * Complex.exp (φ * I)) (v * Complex.exp (-(φ * I))) = diskSource a R r u v := by
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (-(↑φ * I) / 4) := ⟨_, rfl⟩
  have hζ : ‖ζ‖ = 1 := by
    rw [hζdef, Complex.norm_exp]
    simp
  have hζ4 : ζ ^ 4 = Complex.exp (-(↑φ * I)) := by
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcζ4 : conj ζ ^ 4 = Complex.exp (↑φ * I) := by
    rw [← map_pow, hζ4, ← Complex.exp_conj]
    congr 1
    simp
  have hPQ : Complex.exp (↑φ * I) * Complex.exp (-(↑φ * I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hpt : ∀ z : ℂ,
      ((‖ζ * z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖ζ * z‖ ^ 2 : ℝ) : ℂ) +
        (I / 4) * ((u * Complex.exp (φ * I)) * (ζ * z) ^ 4 +
          (v * Complex.exp (-(φ * I))) * conj (ζ * z) ^ 4))
      = ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
        (I / 4) * (u * z ^ 4 + v * conj z ^ 4)) := by
    intro z
    have h1 : ‖ζ * z‖ = ‖z‖ := by rw [norm_mul, hζ, one_mul]
    have h2 : (ζ * z) ^ 4 = Complex.exp (-(↑φ * I)) * z ^ 4 := by rw [mul_pow, hζ4]
    have h3 : conj (ζ * z) ^ 4 = Complex.exp (↑φ * I) * conj z ^ 4 := by
      rw [map_mul, mul_pow, hcζ4]
    rw [h1, h2, h3]
    congr 2
    linear_combination (I / 4 * (u * z ^ 4 + v * conj z ^ 4)) * hPQ
  unfold diskSource
  apply setIntegral_ball_rot_eq R ζ hζ
  intro z
  exact hpt z

lemma hasDerivAt_diskFun (a : ℝ) (r : ℕ) (u v z s : ℂ) :
    HasDerivAt (fun t => diskFun a r u v t z) (diskDer a r u v s z) s := by
  unfold diskFun diskDer
  have hE : HasDerivAt (fun t : ℂ => Complex.exp t) (Complex.exp s) s := by
    simpa using (hasDerivAt_id s).cexp
  have hN : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-Complex.exp (-s)) s := by
    simpa using ((hasDerivAt_id s).neg).cexp
  have hA := (hE.const_mul u).mul_const (z ^ 4)
  have hB := (hN.const_mul v).mul_const (conj z ^ 4)
  have hin := ((hA.add hB).const_mul (I / 4)).const_add
    (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ))
  have hfin := (hin.cexp).const_mul (((‖z‖ ^ (2 * r) : ℝ)) : ℂ)
  have hfin' : HasDerivAt
      (fun t => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
        (I / 4) * (u * Complex.exp t * z ^ 4 + v * Complex.exp (-t) * conj z ^ 4)))
      (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * (Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
        (I / 4) * (u * Complex.exp s * z ^ 4 + v * Complex.exp (-s) * conj z ^ 4)) *
        ((I / 4) * (u * Complex.exp s * z ^ 4 + v * (-Complex.exp (-s)) * conj z ^ 4)))) s := hfin
  refine hfin'.congr_deriv ?_
  ring

lemma continuous_diskFun (a : ℝ) (r : ℕ) (u v s : ℂ) :
    Continuous (fun z => diskFun a r u v s z) := by
  unfold diskFun
  fun_prop

lemma continuous_diskDer_joint (a : ℝ) (r : ℕ) (u v : ℂ) :
    Continuous (fun p : ℂ × ℂ => diskDer a r u v p.1 p.2) := by
  unfold diskDer
  fun_prop

theorem hasDerivAt_diskH (a R : ℝ) (r : ℕ) (u v s : ℂ) :
    HasDerivAt (diskH a R r u v) (∫ z in Metric.closedBall (0 : ℂ) R, diskDer a r u v s z) s := by
  have hfun : diskH a R r u v = fun t => ∫ z in Metric.closedBall (0 : ℂ) R, diskFun a r u v t z :=
    rfl
  rw [hfun]
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s 1).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
    (continuous_diskDer_joint a r u v).continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.closedBall (0 : ℂ) R))
    (F := fun t z => diskFun a r u v t z) (F' := fun t z => diskDer a r u v t z)
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds s one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun t => (continuous_diskFun a r u v t).aestronglyMeasurable
  · exact ((continuous_diskFun a r u v s).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R))
  · exact (continuous_diskDer_joint a r u v |>.comp (Continuous.prodMk_right s)).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_closedBall).mono fun z hz t ht => ?_
    exact hC (t, z) ⟨Metric.ball_subset_closedBall ht, hz⟩
  · exact integrableOn_const (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)).ne
  · exact Filter.Eventually.of_forall fun z t _ => hasDerivAt_diskFun a r u v z t

theorem hasDerivAt_diskH_of (a R : ℝ) (r : ℕ) (u v s : ℂ) :
    DifferentiableAt ℂ (diskH a R r u v) s :=
  (hasDerivAt_diskH a R r u v s).differentiableAt

theorem diskSource_differentiable (a R : ℝ) (r : ℕ) (u v : ℂ) :
    Differentiable ℂ (fun s : ℂ => diskSource a R r (u * Complex.exp s) (v * Complex.exp (-s))) :=
  fun s => hasDerivAt_diskH_of a R r u v s

lemma diskH_shift (a R : ℝ) (r : ℕ) (u v s : ℂ) (t : ℝ) :
    diskH a R r u v (s + (t : ℂ) * I) = diskH a R r u v s := by
  unfold diskH
  have := diskSource_rotate a R r (u * Complex.exp s) (v * Complex.exp (-s)) t
  rw [← this]
  simp only [Complex.exp_add, neg_add, mul_assoc]

lemma diskH_deriv_zero (a R : ℝ) (r : ℕ) (u v s : ℂ) :
    deriv (diskH a R r u v) s = 0 := by
  have hdiff := hasDerivAt_diskH_of a R r u v s
  have hg : HasDerivAt (diskH a R r u v) (deriv (diskH a R r u v) s) (s + ((0 : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    exact hdiff.hasDerivAt
  have hh : HasDerivAt (fun t : ℝ => s + (t : ℂ) * I) I 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add s
    simpa using this
  have hc := hg.scomp 0 hh
  have hconst : HasDerivAt (fun t : ℝ => diskH a R r u v (s + (t : ℂ) * I)) 0 0 := by
    have hfn : (fun t : ℝ => diskH a R r u v (s + (t : ℂ) * I)) = fun _ => diskH a R r u v s :=
      funext fun t => diskH_shift a R r u v s t
    rw [hfn]
    exact hasDerivAt_const _ _
  have hz := hc.unique hconst
  rcases smul_eq_zero.mp hz with h | h
  · exact absurd h Complex.I_ne_zero
  · exact h

theorem diskSource_eq_mul (a R : ℝ) (r : ℕ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    diskSource a R r u v = diskSource a R r (u * v) 1 := by
  have hdz := is_const_of_deriv_eq_zero
    (fun x => hasDerivAt_diskH_of a R r (u : ℂ) (v : ℂ) x)
    (fun x => diskH_deriv_zero a R r (u : ℂ) (v : ℂ) x) ((Real.log v : ℝ) : ℂ) 0
  have e1 : Complex.exp ((Real.log v : ℝ) : ℂ) = (v : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hv]
  have e2 : (v : ℂ) * Complex.exp (-((Real.log v : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hv,
      Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hv.ne')]
  unfold diskH at hdz
  rw [e1, e2] at hdz
  simp only [Complex.exp_zero, mul_one, neg_zero] at hdz
  exact hdz.symm

end Painleve
