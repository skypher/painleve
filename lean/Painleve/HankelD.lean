import Painleve.PlaneHankel
import Painleve.GramD
import Painleve.Polar

/-!
# Gram blocks as Hankel determinants for general `d` (Section 3 of `paper.tex`)

Lemma 3.1 (`lem:source-moments`):
`∑_{k≤p,l≤q} S(p,k) S(q,l) (i/d)^{k+l} M_{kl}^{(r)} = F_r^{(p+q)}(0)` with
`F_r(t) = 𝒲_r(a; e^{t/2})`. The disk integral with two sources depends only on
the product of the sources (rotation invariance and holomorphy), the
derivatives in exponential coordinates produce Stirling numbers, and `R → ∞`
by dominated convergence. This generalizes `DiskSource`, `DiskHankel` and
`PlaneHankel` from `d = 4`.
-/

namespace Painleve
open Complex MeasureTheory
open scoped ComplexConjugate ContDiff
open Filter Topology

variable {d : ℕ}

/-! ### Two sources on a disk -/

noncomputable def diskSourceD (d : ℕ) (a R : ℝ) (r : ℕ) (u v : ℂ) : ℂ :=
  ∫ z in Metric.closedBall (0 : ℂ) R, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (u * z ^ d + v * conj z ^ d))

noncomputable def diskFunD (d : ℕ) (a : ℝ) (r : ℕ) (u v s z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
    (I / d) * (u * Complex.exp s * z ^ d + v * Complex.exp (-s) * conj z ^ d))

noncomputable def diskDerD (d : ℕ) (a : ℝ) (r : ℕ) (u v s z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * (Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
    (I / d) * (u * Complex.exp s * z ^ d + v * Complex.exp (-s) * conj z ^ d)) *
    ((I / d) * (u * Complex.exp s * z ^ d - v * Complex.exp (-s) * conj z ^ d)))

noncomputable def diskHD (d : ℕ) (a R : ℝ) (r : ℕ) (u v : ℂ) (s : ℂ) : ℂ :=
  diskSourceD d a R r (u * Complex.exp s) (v * Complex.exp (-s))

theorem diskSourceD_rotate (hd : 0 < d) (a R : ℝ) (r : ℕ) (u v : ℂ) (φ : ℝ) :
    diskSourceD d a R r (u * Complex.exp (φ * I)) (v * Complex.exp (-(φ * I)))
      = diskSourceD d a R r u v := by
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (-(↑φ * I) / d) := ⟨_, rfl⟩
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hζ : ‖ζ‖ = 1 := by
    rw [hζdef, Complex.norm_exp]
    simp [Complex.div_re]
  have hζd : ζ ^ d = Complex.exp (-(↑φ * I)) := by
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  have hcζd : conj ζ ^ d = Complex.exp (↑φ * I) := by
    rw [← map_pow, hζd, ← Complex.exp_conj]
    congr 1
    simp
  have hPQ : Complex.exp (↑φ * I) * Complex.exp (-(↑φ * I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hpt : ∀ z : ℂ,
      ((‖ζ * z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖ζ * z‖ ^ 2 : ℝ) : ℂ) +
        (I / d) * ((u * Complex.exp (φ * I)) * (ζ * z) ^ d +
          (v * Complex.exp (-(φ * I))) * conj (ζ * z) ^ d))
      = ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
        (I / d) * (u * z ^ d + v * conj z ^ d)) := by
    intro z
    have h1 : ‖ζ * z‖ = ‖z‖ := by rw [norm_mul, hζ, one_mul]
    have h2 : (ζ * z) ^ d = Complex.exp (-(↑φ * I)) * z ^ d := by rw [mul_pow, hζd]
    have h3 : conj (ζ * z) ^ d = Complex.exp (↑φ * I) * conj z ^ d := by
      rw [map_mul, mul_pow, hcζd]
    rw [h1, h2, h3]
    congr 2
    linear_combination (I / d * (u * z ^ d + v * conj z ^ d)) * hPQ
  unfold diskSourceD
  apply setIntegral_ball_rot_eq R ζ hζ
  intro z
  exact hpt z

lemma hasDerivAt_diskFunD (a : ℝ) (r : ℕ) (u v z s : ℂ) :
    HasDerivAt (fun t => diskFunD d a r u v t z) (diskDerD d a r u v s z) s := by
  unfold diskFunD diskDerD
  have hE : HasDerivAt (fun t : ℂ => Complex.exp t) (Complex.exp s) s := by
    simpa using (hasDerivAt_id s).cexp
  have hN : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-Complex.exp (-s)) s := by
    simpa using ((hasDerivAt_id s).neg).cexp
  have hA := (hE.const_mul u).mul_const (z ^ d)
  have hB := (hN.const_mul v).mul_const (conj z ^ d)
  have hin := ((hA.add hB).const_mul (I / d)).const_add (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ))
  have hfin := (hin.cexp).const_mul (((‖z‖ ^ (2 * r) : ℝ)) : ℂ)
  have hfin' : HasDerivAt
      (fun t => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
        (I / d) * (u * Complex.exp t * z ^ d + v * Complex.exp (-t) * conj z ^ d)))
      (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * (Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) +
        (I / d) * (u * Complex.exp s * z ^ d + v * Complex.exp (-s) * conj z ^ d)) *
        ((I / d) * (u * Complex.exp s * z ^ d + v * (-Complex.exp (-s)) * conj z ^ d)))) s := hfin
  refine hfin'.congr_deriv ?_
  ring

lemma continuous_diskFunD (a : ℝ) (r : ℕ) (u v s : ℂ) :
    Continuous (fun z => diskFunD d a r u v s z) := by
  unfold diskFunD; fun_prop

lemma continuous_diskDerD_joint (a : ℝ) (r : ℕ) (u v : ℂ) :
    Continuous (fun p : ℂ × ℂ => diskDerD d a r u v p.1 p.2) := by
  unfold diskDerD; fun_prop

theorem hasDerivAt_diskHD (a R : ℝ) (r : ℕ) (u v s : ℂ) :
    HasDerivAt (diskHD d a R r u v)
      (∫ z in Metric.closedBall (0 : ℂ) R, diskDerD d a r u v s z) s := by
  have hfun : diskHD d a R r u v
      = fun t => ∫ z in Metric.closedBall (0 : ℂ) R, diskFunD d a r u v t z := rfl
  rw [hfun]
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s 1).prod
    (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
    (continuous_diskDerD_joint a r u v).continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Metric.closedBall (0 : ℂ) R))
    (F := fun t z => diskFunD d a r u v t z) (F' := fun t z => diskDerD d a r u v t z)
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds s one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun t =>
      (continuous_diskFunD a r u v t).aestronglyMeasurable
  · exact ((continuous_diskFunD a r u v s).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R))
  · exact (continuous_diskDerD_joint a r u v |>.comp
      (Continuous.prodMk_right s)).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_closedBall).mono fun z hz t ht => ?_
    exact hC (t, z) ⟨Metric.ball_subset_closedBall ht, hz⟩
  · exact integrableOn_const (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)).ne
  · exact Filter.Eventually.of_forall fun z t _ => hasDerivAt_diskFunD a r u v z t

lemma diskHD_shift (hd : 0 < d) (a R : ℝ) (r : ℕ) (u v s : ℂ) (t : ℝ) :
    diskHD d a R r u v (s + (t : ℂ) * I) = diskHD d a R r u v s := by
  unfold diskHD
  have := diskSourceD_rotate hd a R r (u * Complex.exp s) (v * Complex.exp (-s)) t
  rw [← this]
  simp only [Complex.exp_add, neg_add, mul_assoc]

lemma diskHD_deriv_zero (hd : 0 < d) (a R : ℝ) (r : ℕ) (u v s : ℂ) :
    deriv (diskHD d a R r u v) s = 0 := by
  have hdiff := (hasDerivAt_diskHD (d := d) a R r u v s).differentiableAt
  have hg : HasDerivAt (diskHD d a R r u v) (deriv (diskHD d a R r u v) s)
      (s + ((0 : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    exact hdiff.hasDerivAt
  have hh : HasDerivAt (fun t : ℝ => s + (t : ℂ) * I) I 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add s
    simpa using this
  have hc := hg.scomp 0 hh
  have hconst : HasDerivAt (fun t : ℝ => diskHD d a R r u v (s + (t : ℂ) * I)) 0 0 := by
    have hfn : (fun t : ℝ => diskHD d a R r u v (s + (t : ℂ) * I))
        = fun _ => diskHD d a R r u v s := funext fun t => diskHD_shift hd a R r u v s t
    rw [hfn]
    exact hasDerivAt_const _ _
  have hz := hc.unique hconst
  rcases smul_eq_zero.mp hz with h | h
  · exact absurd h Complex.I_ne_zero
  · exact h

theorem diskSourceD_eq_mul (hd : 0 < d) (a R : ℝ) (r : ℕ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    diskSourceD d a R r u v = diskSourceD d a R r (u * v) 1 := by
  have hdz := is_const_of_deriv_eq_zero
    (fun x => (hasDerivAt_diskHD (d := d) a R r (u : ℂ) (v : ℂ) x).differentiableAt)
    (fun x => diskHD_deriv_zero hd a R r (u : ℂ) (v : ℂ) x) ((Real.log v : ℝ) : ℂ) 0
  have e1 : Complex.exp ((Real.log v : ℝ) : ℂ) = (v : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hv]
  have e2 : (v : ℂ) * Complex.exp (-((Real.log v : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hv,
      Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hv.ne')]
  unfold diskHD at hdz
  rw [e1, e2] at hdz
  simp only [Complex.exp_zero, mul_one, neg_zero] at hdz
  exact hdz.symm

/-! ### The truncated identity -/

noncomputable def diskMomD (d : ℕ) (a R : ℝ) (r k l : ℕ) : ℂ :=
  ∫ z in Metric.closedBall (0 : ℂ) R, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) *
    conj z ^ (d * l) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d))

noncomputable def cfunD (d : ℕ) (z : ℂ) : ℂ := (I / d) * z ^ d

noncomputable def dfunD (d : ℕ) (z : ℂ) : ℂ := (I / d) * (conj z) ^ d

noncomputable def BpD (d : ℕ) (a : ℝ) (r p : ℕ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + cfunD d z) *
    ∑ k ∈ Finset.range (p + 1), (stirS p k : ℂ) * cfunD d z ^ k

lemma cfunD_cont : Continuous (cfunD d) := by unfold cfunD; fun_prop

lemma dfunD_cont : Continuous (dfunD d) := by unfold dfunD; fun_prop

lemma BpD_cont (a : ℝ) (r p : ℕ) : Continuous (BpD d a r p) := by
  have := cfunD_cont (d := d)
  unfold BpD
  fun_prop

lemma stepAD (a R : ℝ) (r p : ℕ) (t₂ : ℝ) :
    iteratedDeriv p (fun s : ℝ => diskSourceD d a R r ((Real.exp s : ℝ) : ℂ)
        ((Real.exp t₂ : ℝ) : ℂ)) 0
      = ∫ z in Metric.closedBall (0 : ℂ) R,
          BpD d a r p z * Complex.exp (dfunD d z * ((Real.exp t₂ : ℝ) : ℂ)) := by
  have hfun : (fun s : ℝ => diskSourceD d a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ))
      = fun s : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R,
          (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)
            + dfunD d z * ((Real.exp t₂ : ℝ) : ℂ))) z
            * Complex.exp (cfunD d z * ((Real.exp s : ℝ) : ℂ)) := by
    funext s
    unfold diskSourceD
    refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
    simp only [dfunD, cfunD]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hC : Continuous (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + dfunD d z * ((Real.exp t₂ : ℝ) : ℂ))) := by
    have := dfunD_cont (d := d)
    fun_prop
  have key := integral_iter_exp R (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp
    (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + dfunD d z * ((Real.exp t₂ : ℝ) : ℂ))) (cfunD d) hC
    cfunD_cont p
  beta_reduce at key
  rw [hfun, key]
  refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
  unfold BpD
  have hexp : Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + dfunD d z * ((Real.exp t₂ : ℝ) : ℂ))
      * Complex.exp (cfunD d z)
      = Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + cfunD d z)
      * Complex.exp (dfunD d z * ((Real.exp t₂ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  linear_combination ((stirS p k : ℂ) * ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * cfunD d z ^ k) * hexp

lemma G_eqD (hd : 0 < d) (a R : ℝ) (r : ℕ) (t₁ t₂ : ℝ) :
    diskSourceD d a R r ((Real.exp t₁ : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ)
      = diskSourceD d a R r ((Real.exp (t₁ + t₂) : ℝ) : ℂ) 1 := by
  rw [diskSourceD_eq_mul hd a R r (Real.exp t₁) (Real.exp t₂) (Real.exp_pos _) (Real.exp_pos _)]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]

lemma pw_identityD (a : ℝ) (r p q : ℕ) (z : ℂ) :
    ∑ l ∈ Finset.range (q + 1), (stirS q l : ℂ) *
        (BpD d a r p z * dfunD d z ^ l * Complex.exp (dfunD d z))
      = ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
          (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) *
            (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) *
              Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d))) := by
  have hexp : Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + cfunD d z) * Complex.exp (dfunD d z)
      = Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold cfunD dfunD
    ring
  have hc : ∀ k : ℕ, cfunD d z ^ k = (I / d) ^ k * z ^ (d * k) := by
    intro k; unfold cfunD; rw [mul_pow, ← pow_mul]
  have hdd : ∀ l : ℕ, dfunD d z ^ l = (I / d) ^ l * conj z ^ (d * l) := by
    intro l; unfold dfunD; rw [mul_pow, ← pow_mul]
  unfold BpD
  simp only [hc, hdd]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  linear_combination ((stirS q l : ℂ) * (stirS p k : ℂ) * ((‖z‖ ^ (2 * r) : ℝ) : ℂ)
    * (I / d) ^ k * z ^ (d * k) * (I / d) ^ l * conj z ^ (d * l)) * hexp

theorem disk_hankelD (hd : 0 < d) (a R : ℝ) (r p q : ℕ) :
    ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) * diskMomD d a R r k l =
    iteratedDeriv (p + q) (fun t : ℝ => diskSourceD d a R r (Real.exp t : ℂ) 1) 0 := by
  have hL : iteratedDeriv (p + q) (fun t : ℝ => diskSourceD d a R r (Real.exp t : ℂ) 1) 0
      = iteratedDeriv q (fun t₂ : ℝ => iteratedDeriv p
          (fun s : ℝ => diskSourceD d a R r ((Real.exp s : ℝ) : ℂ)
            ((Real.exp t₂ : ℝ) : ℂ)) 0) 0 := by
    rw [iter_add_eq]
    congr 1
    funext t₂
    have hsh : (fun s : ℝ => diskSourceD d a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ))
        = fun s : ℝ => diskSourceD d a R r ((Real.exp (s + t₂) : ℝ) : ℂ) 1 :=
      funext fun s => G_eqD hd a R r s t₂
    have hc : iteratedDeriv p (fun s : ℝ => diskSourceD d a R r ((Real.exp (s + t₂) : ℝ) : ℂ) 1)
        = fun t : ℝ => iteratedDeriv p (fun t' : ℝ => diskSourceD d a R r (Real.exp t' : ℂ) 1)
            (t + t₂) :=
      iteratedDeriv_comp_add_const p (f := fun t' : ℝ => diskSourceD d a R r (Real.exp t' : ℂ) 1)
        (s := t₂)
    rw [hsh, hc]
    simp
  rw [hL]
  have hfun2 : (fun t₂ : ℝ => iteratedDeriv p
      (fun s : ℝ => diskSourceD d a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ)) 0)
      = fun t₂ : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R,
          BpD d a r p z * Complex.exp (dfunD d z * ((Real.exp t₂ : ℝ) : ℂ)) :=
    funext fun t₂ => stepAD a R r p t₂
  rw [hfun2]
  have hB := integral_iter_exp R (BpD d a r p) (dfunD d) (BpD_cont a r p) dfunD_cont q
  beta_reduce at hB
  rw [hB]
  have hSc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hint : ∀ k ∈ Finset.range (p + 1), ∀ l ∈ Finset.range (q + 1),
      Integrable (fun z : ℂ => (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) *
            (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) *
              Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d))))
        (volume.restrict (Metric.closedBall (0 : ℂ) R)) := by
    intro k _ l _
    have hcont : Continuous (fun z : ℂ => (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) *
            (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) *
              Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d)))) := by
      fun_prop
    exact hcont.continuousOn.integrableOn_compact hSc
  symm
  rw [setIntegral_congr_fun measurableSet_closedBall (fun z _ => pw_identityD a r p q z)]
  rw [integral_finsetSum (Finset.range (p + 1)) (fun k hk =>
    integrable_finsetSum (Finset.range (q + 1)) (fun l hl => hint k hk l hl))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [integral_finsetSum (Finset.range (q + 1)) (fun l hl => hint k hk l hl)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [integral_const_mul]
  rfl

/-! ### The full plane -/

noncomputable def plcD (d : ℕ) (z : ℂ) : ℂ := (I / d) * (z ^ d + conj z ^ d)

noncomputable def plIntD (d : ℕ) (a : ℝ) (r : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)
    + (I / d) * ((Real.exp (t / 2) : ℝ) : ℂ) * (z ^ d + conj z ^ d))

lemma plIntD_eq (a : ℝ) (r : ℕ) (t : ℝ) (z : ℂ) :
    plIntD d a r t z = plA a r z * Complex.exp (plcD d z * ((Real.exp (t / 2) : ℝ) : ℂ)) := by
  unfold plIntD plA plcD
  rw [show ∀ N X Y : ℂ, N * Complex.exp X * Complex.exp Y = N * Complex.exp (X + Y) from
    fun N X Y => by rw [mul_assoc, ← Complex.exp_add]]
  congr 2
  ring

lemma plcD_cont : Continuous (plcD d) := by unfold plcD; fun_prop

lemma plIntD_contDiff (a : ℝ) (r : ℕ) (z : ℂ) : ContDiff ℝ ∞ (fun t : ℝ => plIntD d a r t z) := by
  have h : (fun t : ℝ => plIntD d a r t z)
      = fun t : ℝ => plA a r z * Complex.exp (plcD d z * ((Real.exp (t / 2) : ℝ) : ℂ)) :=
    funext fun t => plIntD_eq a r t z
  rw [h]
  have hE : ContDiff ℝ ∞ (fun t : ℝ => ((Real.exp (t / 2) : ℝ) : ℂ)) :=
    contDiff_ofReal'.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))
  exact contDiff_const.mul (contDiff_const.mul hE).cexp

lemma plIntD_formula (a : ℝ) (r j : ℕ) (t : ℝ) (z : ℂ) :
    iteratedDeriv j (fun s => plIntD d a r s z) t
      = ((1 / 2 : ℝ) ^ j) • ∑ k ∈ Finset.range (j + 1), (stirS j k : ℂ) *
          ((Real.exp (1 / 2 * t) : ℝ) : ℂ) ^ k *
          (plA a r z * plcD d z ^ k * Complex.exp (plcD d z * ((Real.exp (1 / 2 * t) : ℝ) : ℂ))) := by
  have hfun : (fun s => plIntD d a r s z)
      = fun s => (fun u : ℝ => plA a r z * Complex.exp (plcD d z * ((Real.exp u : ℝ) : ℂ)))
          (1 / 2 * s) := by
    funext s
    simp only []
    rw [plIntD_eq]
    congr 3
    ring_nf
  have hg : ContDiff ℝ j (fun u : ℝ => plA a r z * Complex.exp (plcD d z * ((Real.exp u : ℝ) : ℂ))) := by
    have hE : ContDiff ℝ j (fun u : ℝ => ((Real.exp u : ℝ) : ℂ)) :=
      (contDiff_ofReal_gen j).comp Real.contDiff_exp
    exact contDiff_const.mul (contDiff_const.mul hE).cexp
  rw [hfun]
  rw [iteratedDeriv_comp_const_smul hg (1 / 2 : ℝ)]
  simp only []
  rw [iteratedDeriv_exp_comp]

/-- `F_r(t) = 𝒲_r(a; e^{t/2})`. -/
noncomputable def eqSrcD (d : ℕ) (a : ℝ) (r : ℕ) (t : ℝ) : ℂ := ∫ z : ℂ, plIntD d a r t z

lemma eqSrcD_eq_srcW (a : ℝ) (r : ℕ) (t : ℝ) : eqSrcD d a r t = srcW d r a (Real.exp (t / 2)) := by
  unfold eqSrcD plIntD srcW
  congr 1; funext z; congr 3; ring

noncomputable def plBndD (d : ℕ) (a : ℝ) (r j : ℕ) (z : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), ((stirS j k : ℝ) * 4 ^ k) *
    (‖z‖ ^ (2 * r + d * k) * Real.exp (-a * ‖z‖ ^ 2))

lemma plBndD_integrable (a : ℝ) (ha : 0 < a) (r j : ℕ) : Integrable (plBndD d a r j) := by
  unfold plBndD
  exact integrable_finsetSum _ (fun k _ => (integrable_norm_gauss a ha (2 * r + d * k)).const_mul _)

lemma plcD_re (z : ℂ) (x : ℝ) : (plcD d z * ((x : ℝ) : ℂ)).re = 0 := by
  obtain ⟨w, hw⟩ := conj_pow_add_real (d := d) z
  unfold plcD
  rw [hw]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

lemma norm_plcD_exp (z : ℂ) (x : ℝ) : ‖Complex.exp (plcD d z * ((x : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp, plcD_re z x, Real.exp_zero]

lemma norm_plcD_le (hd : 0 < d) (z : ℂ) : ‖plcD d z‖ ≤ 2 * ‖z‖ ^ d := by
  unfold plcD
  have h1 : ‖z ^ d + conj z ^ d‖ ≤ ‖z‖ ^ d + ‖z‖ ^ d := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow, Complex.norm_conj]
  have hI : ‖I / (d : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_I, Complex.norm_natCast]
    rw [div_le_one (by exact_mod_cast hd)]
    exact_mod_cast hd
  rw [norm_mul]
  calc ‖I / (d : ℂ)‖ * ‖z ^ d + conj z ^ d‖ ≤ 1 * (‖z‖ ^ d + ‖z‖ ^ d) :=
        mul_le_mul hI h1 (norm_nonneg _) zero_le_one
    _ = 2 * ‖z‖ ^ d := by ring

lemma plIntD_bound (hd : 0 < d) (a : ℝ) (r j : ℕ) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1)
    (z : ℂ) : ‖iteratedDeriv j (fun s => plIntD d a r s z) t‖ ≤ plBndD d a r j z := by
  rw [plIntD_formula, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hte : |t| < 1 := by simpa [Real.dist_eq] using ht
  have hsx : 1 / 2 * t < 1 / 2 := by rw [abs_lt] at hte; linarith
  have h12 : Real.exp (1 / 2) < 2 := by
    have e2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]
  have hEx : Real.exp (1 / 2 * t) ≤ 2 := (Real.exp_le_exp.mpr hsx.le).trans h12.le
  have hpow : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.exp (1 / 2 * t) := (Real.exp_pos _).le
  refine (mul_le_of_le_one_left (norm_nonneg _) hpow).trans ?_
  refine (norm_sum_le _ _).trans ?_
  unfold plBndD
  refine Finset.sum_le_sum (fun k _ => ?_)
  simp only [norm_mul, norm_pow]
  rw [norm_plA, norm_plcD_exp, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hpos]
  have hc := norm_plcD_le hd z
  have hAE : 0 ≤ ‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) := by positivity
  have hEk : (Real.exp (1 / 2 * t)) ^ k ≤ 2 ^ k := pow_le_pow_left₀ hpos hEx k
  have hck : ‖plcD d z‖ ^ k ≤ (2 * ‖z‖ ^ d) ^ k := pow_le_pow_left₀ (norm_nonneg _) hc k
  have hs0 : (0 : ℝ) ≤ (stirS j k : ℝ) := Nat.cast_nonneg _
  have e1 : ‖z‖ ^ (2 * r + d * k) = ‖z‖ ^ (2 * r) * (‖z‖ ^ d) ^ k := by
    rw [← pow_mul, ← pow_add]
  rw [e1]
  have hpk : 0 ≤ ‖plcD d z‖ ^ k := by positivity
  have hsE : 0 ≤ (Real.exp (1 / 2 * t)) ^ k := by positivity
  calc (stirS j k : ℝ) * (Real.exp (1 / 2 * t)) ^ k * (‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2)
        * ‖plcD d z‖ ^ k * 1)
      ≤ (stirS j k : ℝ) * 2 ^ k * (‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) *
          (2 * ‖z‖ ^ d) ^ k) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hEk hs0) _ (by positivity) (by positivity)
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hck hAE
    _ = (stirS j k : ℝ) * 4 ^ k * (‖z‖ ^ (2 * r) * (‖z‖ ^ d) ^ k * Real.exp (-a * ‖z‖ ^ 2)) := by
        rw [mul_pow, show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
        ring

lemma plIntD_meas (a : ℝ) (r j : ℕ) (t : ℝ) :
    Continuous (fun z : ℂ => iteratedDeriv j (fun s => plIntD d a r s z) t) := by
  have h : (fun z : ℂ => iteratedDeriv j (fun s => plIntD d a r s z) t)
      = fun z : ℂ => ((1 / 2 : ℝ) ^ j) • ∑ k ∈ Finset.range (j + 1), (stirS j k : ℂ) *
          ((Real.exp (1 / 2 * t) : ℝ) : ℂ) ^ k *
          (plA a r z * plcD d z ^ k * Complex.exp (plcD d z * ((Real.exp (1 / 2 * t) : ℝ) : ℂ))) :=
    funext fun z => plIntD_formula a r j t z
  rw [h]
  have := plA_cont a r
  have := plcD_cont (d := d)
  fun_prop

lemma plIntD_deriv (hd : 0 < d) (a : ℝ) (ha : 0 < a) (r : ℕ) (μ : Measure ℂ) (hμ : μ ≤ volume)
    (m : ℕ) :
    iteratedDeriv m (fun t => ∫ z, plIntD d a r t z ∂μ) 0
      = ∫ z, iteratedDeriv m (fun s => plIntD d a r s z) 0 ∂μ := by
  refine iteratedDeriv_integral (fun t z => plIntD d a r t z) (t₀ := 0) (ε := 1) one_pos m
    (fun z => plIntD_contDiff a r z) ?_ (fun j z => plBndD d a r j z) ?_ ?_ 0
    (Metric.mem_ball_self one_pos)
  · intro j _ t
    exact (plIntD_meas a r j t).aestronglyMeasurable
  · intro j _
    exact (plBndD_integrable a ha r j).mono_measure hμ
  · intro j _ t ht z
    exact plIntD_bound hd a r j t ht z

lemma wmomD_tendsto (a : ℝ) (ha : 0 < a) (r k l : ℕ) :
    Tendsto (fun n : ℕ => diskMomD d a (n : ℝ) r k l) atTop (𝓝 (wmomD d a r k l)) := by
  have hb : ∀ z : ℂ, ‖((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) *
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d))‖
        ≤ ‖z‖ ^ (2 * r + d * k + d * l) * Real.exp (-a * ‖z‖ ^ 2) := by
    intro z
    have hdn : ‖Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d))‖
        = Real.exp (-a * ‖z‖ ^ 2) := by
      have h := norm_densityD (d := d) a z
      unfold densityD at h
      exact h
    rw [norm_mul, norm_mul, norm_mul, hdn, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply le_of_eq
    ring
  have h := plLim (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) *
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d)))
    (fun z : ℂ => ‖z‖ ^ (2 * r + d * k + d * l) * Real.exp (-a * ‖z‖ ^ 2))
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (integrable_norm_gauss a ha (2 * r + d * k + d * l)) hb
  have hw : wmomD d a r k l = ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) *
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d)) := rfl
  rw [hw]
  exact h

lemma diskSourceD_eq_plInt (hd : 0 < d) (a R : ℝ) (r : ℕ) (t : ℝ) :
    diskSourceD d a R r ((Real.exp t : ℝ) : ℂ) 1
      = ∫ z in Metric.closedBall (0 : ℂ) R, plIntD d a r t z := by
  have e := diskSourceD_eq_mul hd a R r (Real.exp (t / 2)) (Real.exp (t / 2))
    (Real.exp_pos _) (Real.exp_pos _)
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_halves] at e
  rw [← e]
  unfold diskSourceD
  refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
  unfold plIntD
  congr 2
  ring

/-- **Lemma 3.1** (`lem:source-moments`). -/
theorem plane_hankelD (hd : 0 < d) (a : ℝ) (ha : 0 < a) (r p q : ℕ) :
    ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) * wmomD d a r k l =
    iteratedDeriv (p + q) (eqSrcD d a r) 0 := by
  have hEq : iteratedDeriv (p + q) (eqSrcD d a r) 0
      = ∫ z : ℂ, iteratedDeriv (p + q) (fun s => plIntD d a r s z) 0 :=
    plIntD_deriv hd a ha r volume le_rfl (p + q)
  have hL : ∀ n : ℕ, (∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) * diskMomD d a (n : ℝ) r k l)
      = ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ),
          iteratedDeriv (p + q) (fun s => plIntD d a r s z) 0 := by
    intro n
    rw [disk_hankelD hd a (n : ℝ) r p q]
    have h2 : (fun t : ℝ => diskSourceD d a (n : ℝ) r ((Real.exp t : ℝ) : ℂ) 1)
        = fun t : ℝ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ), plIntD d a r t z :=
      funext fun t => diskSourceD_eq_plInt hd a (n : ℝ) r t
    rw [h2]
    exact plIntD_deriv hd a ha r (volume.restrict (Metric.closedBall (0 : ℂ) (n : ℝ)))
      Measure.restrict_le_self (p + q)
  have hA : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) * diskMomD d a (n : ℝ) r k l)
      atTop (𝓝 (∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
        (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) * wmomD d a r k l)) :=
    tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
      (wmomD_tendsto a ha r k l).const_mul _
  have hB : Tendsto (fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ),
      iteratedDeriv (p + q) (fun s => plIntD d a r s z) 0) atTop
      (𝓝 (∫ z : ℂ, iteratedDeriv (p + q) (fun s => plIntD d a r s z) 0)) :=
    plLim (fun z => iteratedDeriv (p + q) (fun s => plIntD d a r s z) 0)
      (plBndD d a r (p + q)) (plIntD_meas a r (p + q) 0).aestronglyMeasurable
      (plBndD_integrable a ha r (p + q))
      (fun z => plIntD_bound hd a r (p + q) 0 (Metric.mem_ball_self one_pos) z)
  have hfun : (fun n : ℕ => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / d) ^ (k + l) * diskMomD d a (n : ℝ) r k l)
      = fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ),
          iteratedDeriv (p + q) (fun s => plIntD d a r s z) 0 :=
    funext fun n => hL n
  rw [hfun] at hA
  have hu := tendsto_nhds_unique hA hB
  rw [hEq]
  exact hu

end Painleve
