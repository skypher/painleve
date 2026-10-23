import Painleve.DiskHankel
import Painleve.Moments
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Painleve
open Complex MeasureTheory
open scoped ComplexConjugate ContDiff
open Filter Topology

/-- Gaussian-times-power majorant on `ℂ`. -/
lemma integrable_norm_gauss (a : ℝ) (ha : 0 < a) (m : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ m * Real.exp (-a * ‖z‖ ^ 2)) := by
  obtain ⟨C, hC⟩ := poly_gauss a ha m
  refine Integrable.mono' ((integrable_gauss a ha).const_mul C) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hC ‖z‖ (norm_nonneg z)

noncomputable def plA (a : ℝ) (r : ℕ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ))

noncomputable def plc (z : ℂ) : ℂ := (I / 4) * (z ^ 4 + conj z ^ 4)

/-- The equal-coupling integrand at parameter `t`. -/
noncomputable def plInt (a : ℝ) (r : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)
    + (I / 4) * ((Real.exp (t / 2) : ℝ) : ℂ) * (z ^ 4 + conj z ^ 4))

lemma plInt_eq (a : ℝ) (r : ℕ) (t : ℝ) (z : ℂ) :
    plInt a r t z = plA a r z * Complex.exp (plc z * ((Real.exp (t / 2) : ℝ) : ℂ)) := by
  unfold plInt plA plc
  have e := Complex.exp_add (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ))
    ((I / 4) * (z ^ 4 + conj z ^ 4) * ((Real.exp (t / 2) : ℝ) : ℂ))
  have hassoc : ∀ N X Y : ℂ, N * Complex.exp X * Complex.exp Y = N * (Complex.exp X * Complex.exp Y) :=
    fun N X Y => mul_assoc _ _ _
  rw [hassoc, ← e]
  congr 2
  ring_nf

lemma contDiff_ofReal_gen (n : WithTop ℕ∞) : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

lemma plA_cont (a : ℝ) (r : ℕ) : Continuous (plA a r) := by
  unfold plA
  fun_prop

lemma plc_cont : Continuous plc := by
  unfold plc
  fun_prop

lemma plInt_contDiff (a : ℝ) (r : ℕ) (z : ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => plInt a r t z) := by
  have h : (fun t : ℝ => plInt a r t z)
      = fun t : ℝ => plA a r z * Complex.exp (plc z * ((Real.exp (t / 2) : ℝ) : ℂ)) :=
    funext fun t => plInt_eq a r t z
  rw [h]
  have hE : ContDiff ℝ ∞ (fun t : ℝ => ((Real.exp (t / 2) : ℝ) : ℂ)) :=
    contDiff_ofReal'.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))
  exact contDiff_const.mul (contDiff_const.mul hE).cexp

lemma plInt_formula (a : ℝ) (r j : ℕ) (t : ℝ) (z : ℂ) :
    iteratedDeriv j (fun s => plInt a r s z) t
      = ((1 / 2 : ℝ) ^ j) • ∑ k ∈ Finset.range (j + 1), (stirS j k : ℂ) *
          ((Real.exp (1 / 2 * t) : ℝ) : ℂ) ^ k *
          (plA a r z * plc z ^ k * Complex.exp (plc z * ((Real.exp (1 / 2 * t) : ℝ) : ℂ))) := by
  have hfun : (fun s => plInt a r s z)
      = fun s => (fun u : ℝ => plA a r z * Complex.exp (plc z * ((Real.exp u : ℝ) : ℂ))) (1 / 2 * s) := by
    funext s
    simp only []
    rw [plInt_eq]
    congr 3
    ring_nf
  have hg : ContDiff ℝ j (fun u : ℝ => plA a r z * Complex.exp (plc z * ((Real.exp u : ℝ) : ℂ))) := by
    have hE : ContDiff ℝ j (fun u : ℝ => ((Real.exp u : ℝ) : ℂ)) :=
      (contDiff_ofReal_gen j).comp Real.contDiff_exp
    exact contDiff_const.mul (contDiff_const.mul hE).cexp
  rw [hfun]
  rw [iteratedDeriv_comp_const_smul hg (1 / 2 : ℝ)]
  simp only []
  rw [iteratedDeriv_exp_comp]

/-- Weighted planar moments. -/
noncomputable def wmom (a : ℝ) (r k l : ℕ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))

/-- The equal-coupling planar source at coupling e^{t/2}. -/
noncomputable def eqSrc (a : ℝ) (r : ℕ) (t : ℝ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (Real.exp (t / 2) : ℂ) * (z ^ 4 + conj z ^ 4))

/-- Majorant of the `t`-derivatives of the integrand, uniform in `t ∈ (-1,1)`. -/
noncomputable def plBnd (a : ℝ) (r j : ℕ) (z : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), ((stirS j k : ℝ) * 2 ^ k) *
    (‖z‖ ^ (2 * r + 4 * k) * Real.exp (-a * ‖z‖ ^ 2))

lemma plBnd_integrable (a : ℝ) (ha : 0 < a) (r j : ℕ) : Integrable (plBnd a r j) := by
  unfold plBnd
  exact integrable_finsetSum _ (fun k _ => (integrable_norm_gauss a ha (2 * r + 4 * k)).const_mul _)

lemma plc_re (z : ℂ) (x : ℝ) : (plc z * ((x : ℝ) : ℂ)).re = 0 := by
  have hw : (z ^ 4 + conj z ^ 4).im = 0 := by
    rw [← map_pow, Complex.add_im, Complex.conj_im]
    ring_nf
  unfold plc
  simp [Complex.mul_re, Complex.mul_im, hw]

lemma norm_plc_exp (z : ℂ) (x : ℝ) : ‖Complex.exp (plc z * ((x : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp, plc_re z x, Real.exp_zero]

lemma norm_plc_le (z : ℂ) : ‖plc z‖ ≤ ‖z‖ ^ 4 := by
  unfold plc
  have h1 : ‖z ^ 4 + conj z ^ 4‖ ≤ ‖z‖ ^ 4 + ‖z‖ ^ 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow, Complex.norm_conj]
  have hI : ‖I / 4‖ = 1 / 4 := by simp
  rw [norm_mul, hI]
  nlinarith [norm_nonneg z, pow_nonneg (norm_nonneg z) 4]

lemma norm_plA (a : ℝ) (r : ℕ) (z : ℂ) :
    ‖plA a r z‖ = ‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) := by
  have hre : (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)).re = -a * ‖z‖ ^ 2 := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold plA
  rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

lemma plInt_bound (a : ℝ) (r j : ℕ) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) (z : ℂ) :
    ‖iteratedDeriv j (fun s => plInt a r s z) t‖ ≤ plBnd a r j z := by
  rw [plInt_formula, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hte : |t| < 1 := by simpa [Real.dist_eq] using ht
  have hsx : 1 / 2 * t < 1 / 2 := by
    rw [abs_lt] at hte; linarith
  have h12 : Real.exp (1 / 2) < 2 := by
    have e2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]
  have hEx : Real.exp (1 / 2 * t) ≤ 2 :=
    (Real.exp_le_exp.mpr hsx.le).trans h12.le
  have hpow : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : 0 ≤ Real.exp (1 / 2 * t) := (Real.exp_pos _).le
  refine (mul_le_of_le_one_left (norm_nonneg _) hpow).trans ?_
  refine (norm_sum_le _ _).trans ?_
  unfold plBnd
  refine Finset.sum_le_sum (fun k _ => ?_)
  simp only [norm_mul, norm_pow]
  rw [norm_plA, norm_plc_exp, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hpos]
  have hc := norm_plc_le z
  have hAE : 0 ≤ ‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) := by positivity
  have hEk : (Real.exp (1 / 2 * t)) ^ k ≤ 2 ^ k := pow_le_pow_left₀ hpos hEx k
  have hck : ‖plc z‖ ^ k ≤ (‖z‖ ^ 4) ^ k := pow_le_pow_left₀ (norm_nonneg _) hc k
  have hs0 : (0 : ℝ) ≤ (stirS j k : ℝ) := Nat.cast_nonneg _
  have e1 : ‖z‖ ^ (2 * r + 4 * k) = ‖z‖ ^ (2 * r) * (‖z‖ ^ 4) ^ k := by
    rw [← pow_mul, ← pow_add]
  rw [e1]
  have hpk : 0 ≤ ‖plc z‖ ^ k := by positivity
  have hsE : 0 ≤ (Real.exp (1 / 2 * t)) ^ k := by positivity
  calc (stirS j k : ℝ) * (Real.exp (1 / 2 * t)) ^ k * (‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2)
        * ‖plc z‖ ^ k * 1)
      ≤ (stirS j k : ℝ) * 2 ^ k * (‖z‖ ^ (2 * r) * Real.exp (-a * ‖z‖ ^ 2) * (‖z‖ ^ 4) ^ k) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hEk hs0) _ (by positivity) (by positivity)
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hck hAE
    _ = (stirS j k : ℝ) * 2 ^ k * (‖z‖ ^ (2 * r) * (‖z‖ ^ 4) ^ k * Real.exp (-a * ‖z‖ ^ 2)) := by ring

lemma plInt_meas (a : ℝ) (r j : ℕ) (t : ℝ) :
    Continuous (fun z : ℂ => iteratedDeriv j (fun s => plInt a r s z) t) := by
  have h : (fun z : ℂ => iteratedDeriv j (fun s => plInt a r s z) t)
      = fun z : ℂ => ((1 / 2 : ℝ) ^ j) • ∑ k ∈ Finset.range (j + 1), (stirS j k : ℂ) *
          ((Real.exp (1 / 2 * t) : ℝ) : ℂ) ^ k *
          (plA a r z * plc z ^ k * Complex.exp (plc z * ((Real.exp (1 / 2 * t) : ℝ) : ℂ))) :=
    funext fun z => plInt_formula a r j t z
  rw [h]
  have := plA_cont a r
  have := plc_cont
  fun_prop

/-- Differentiation under the integral sign, at `0`, for `μ ≤ volume`. -/
lemma plInt_deriv (a : ℝ) (ha : 0 < a) (r : ℕ) (μ : Measure ℂ) (hμ : μ ≤ volume) (m : ℕ) :
    iteratedDeriv m (fun t => ∫ z, plInt a r t z ∂μ) 0
      = ∫ z, iteratedDeriv m (fun s => plInt a r s z) 0 ∂μ := by
  refine iteratedDeriv_integral (fun t z => plInt a r t z) (t₀ := 0) (ε := 1) one_pos m
    (fun z => plInt_contDiff a r z) ?_ (fun j z => plBnd a r j z) ?_ ?_ 0
    (Metric.mem_ball_self one_pos)
  · intro j _ t
    exact (plInt_meas a r j t).aestronglyMeasurable
  · intro j _
    exact (plBnd_integrable a ha r j).mono_measure hμ
  · intro j _ t ht z
    exact plInt_bound a r j t ht z

/-- Dominated convergence along the exhaustion by closed balls. -/
lemma plLim (f : ℂ → ℂ) (g : ℂ → ℝ) (hf : AEStronglyMeasurable f volume)
    (hg : Integrable g volume) (hb : ∀ z, ‖f z‖ ≤ g z) :
    Tendsto (fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ), f z) atTop
      (𝓝 (∫ z, f z)) := by
  have hind : ∀ (n : ℕ) (z : ℂ),
      ‖(Metric.closedBall (0 : ℂ) (n : ℝ)).indicator f z‖ ≤ ‖f z‖ := by
    intro n z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (n : ℝ)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  have key : (fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ), f z)
      = fun n : ℕ => ∫ z, (Metric.closedBall (0 : ℂ) (n : ℝ)).indicator f z :=
    funext fun n => (integral_indicator measurableSet_closedBall).symm
  rw [key]
  refine tendsto_integral_of_dominated_convergence g
    (fun n => hf.indicator measurableSet_closedBall) hg
    (fun n => Filter.Eventually.of_forall fun z => (hind n z).trans (hb z))
    (Filter.Eventually.of_forall fun z => ?_)
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have hz : z ∈ Metric.closedBall (0 : ℂ) (n : ℝ) := by
    rw [mem_closedBall_zero_iff]
    exact hN.trans (by exact_mod_cast hn)
  exact (Set.indicator_of_mem hz f).symm

lemma wmom_tendsto (a : ℝ) (ha : 0 < a) (r k l : ℕ) :
    Tendsto (fun n : ℕ => diskMom a (n : ℝ) r k l) atTop (𝓝 (wmom a r k l)) := by
  have hb : ∀ z : ℂ, ‖((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))‖
        ≤ ‖z‖ ^ (2 * r + 4 * k + 4 * l) * Real.exp (-a * ‖z‖ ^ 2) := by
    intro z
    have hd : ‖Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))‖
        = Real.exp (-a * ‖z‖ ^ 2) := by
      have h := norm_density a z
      unfold density at h
      exact h
    rw [norm_mul, norm_mul, norm_mul, hd, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply le_of_eq
    ring
  have h := plLim (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
      Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4)))
    (fun z : ℂ => ‖z‖ ^ (2 * r + 4 * k + 4 * l) * Real.exp (-a * ‖z‖ ^ 2))
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (integrable_norm_gauss a ha (2 * r + 4 * k + 4 * l)) hb
  exact h

/-- Disk side: the disk source at `e^t` is the `plInt` integral over the closed ball. -/
lemma diskSource_eq_plInt (a R : ℝ) (r : ℕ) (t : ℝ) :
    diskSource a R r ((Real.exp t : ℝ) : ℂ) 1
      = ∫ z in Metric.closedBall (0 : ℂ) R, plInt a r t z := by
  have e := diskSource_eq_mul a R r (Real.exp (t / 2)) (Real.exp (t / 2))
    (Real.exp_pos _) (Real.exp_pos _)
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_halves] at e
  rw [← e]
  unfold diskSource
  refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
  unfold plInt
  congr 2
  ring

theorem plane_hankel (a : ℝ) (ha : 0 < a) (r p q : ℕ) :
    ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) * wmom a r k l =
    iteratedDeriv (p + q) (eqSrc a r) 0 := by
  have hfunD : (fun t : ℝ => ∫ z : ℂ, plInt a r t z) = eqSrc a r := by
    funext t
    rfl
  have hEq : iteratedDeriv (p + q) (eqSrc a r) 0
      = ∫ z : ℂ, iteratedDeriv (p + q) (fun s => plInt a r s z) 0 := by
    rw [← hfunD]
    exact plInt_deriv a ha r volume le_rfl (p + q)
  have hL : ∀ n : ℕ, (∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) * diskMom a (n : ℝ) r k l)
      = ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ), iteratedDeriv (p + q) (fun s => plInt a r s z) 0 := by
    intro n
    rw [disk_hankel a (n : ℝ) r p q]
    have h2 : (fun t : ℝ => diskSource a (n : ℝ) r ((Real.exp t : ℝ) : ℂ) 1)
        = fun t : ℝ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ), plInt a r t z :=
      funext fun t => diskSource_eq_plInt a (n : ℝ) r t
    rw [h2]
    exact plInt_deriv a ha r (volume.restrict (Metric.closedBall (0 : ℂ) (n : ℝ)))
      Measure.restrict_le_self (p + q)
  have hA : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) * diskMom a (n : ℝ) r k l)
      atTop (𝓝 (∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
        (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) * wmom a r k l)) :=
    tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
      (wmom_tendsto a ha r k l).const_mul _
  have hB : Tendsto (fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ),
      iteratedDeriv (p + q) (fun s => plInt a r s z) 0) atTop
      (𝓝 (∫ z : ℂ, iteratedDeriv (p + q) (fun s => plInt a r s z) 0)) :=
    plLim (fun z => iteratedDeriv (p + q) (fun s => plInt a r s z) 0)
      (plBnd a r (p + q)) (plInt_meas a r (p + q) 0).aestronglyMeasurable
      (plBnd_integrable a ha r (p + q))
      (fun z => plInt_bound a r (p + q) 0 (Metric.mem_ball_self one_pos) z)
  have hfun : (fun n : ℕ => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) * diskMom a (n : ℝ) r k l)
      = fun n : ℕ => ∫ z in Metric.closedBall (0 : ℂ) (n : ℝ),
          iteratedDeriv (p + q) (fun s => plInt a r s z) 0 :=
    funext fun n => hL n
  rw [hfun] at hA
  have hu := tendsto_nhds_unique hA hB
  rw [hEq]
  exact hu

end Painleve
