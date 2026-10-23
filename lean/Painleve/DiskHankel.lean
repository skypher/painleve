import Painleve.Calc
import Painleve.DiffInt
import Painleve.DiskSource

namespace Painleve
open Complex MeasureTheory
open scoped ComplexConjugate ContDiff

lemma contDiff_ofReal' : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

lemma iteratedDeriv_expLin (C c : ℂ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => C * Complex.exp (c * (x : ℂ)))
      = fun x : ℝ => C * c ^ k * Complex.exp (c * (x : ℂ)) := by
  induction k with
  | zero => funext x; simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) x :=
      ((hasDerivAt_id x).ofReal_comp).const_mul c
    have hd := ((h1.cexp).const_mul (C * c ^ k))
    exact hd.deriv.trans (by ring)

lemma contDiff_expLin (C c : ℂ) :
    ContDiff ℝ ∞ (fun x : ℝ => C * Complex.exp (c * (x : ℂ))) :=
  contDiff_const.mul (contDiff_const.mul contDiff_ofReal').cexp

/-- Derivatives of `s ↦ C·exp(c·e^s)` at any point. -/
lemma iteratedDeriv_exp_comp (C c : ℂ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => C * Complex.exp (c * ((Real.exp s : ℝ) : ℂ))) t
      = ∑ k ∈ Finset.range (j + 1), (stirS j k : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ k *
          (C * c ^ k * Complex.exp (c * ((Real.exp t : ℝ) : ℂ))) := by
  have hΦ : ContDiffOn ℝ ∞ (fun x : ℝ => C * Complex.exp (c * (x : ℂ))) (Set.Ioi 0) :=
    (contDiff_expLin C c).contDiffOn
  have key := iteratedDeriv_comp_exp (fun x : ℝ => C * Complex.exp (c * (x : ℂ))) hΦ j t
  simp only [iteratedDeriv_expLin] at key
  exact key

noncomputable def hankelH (C c : ℂ → ℂ) (j : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (j + 1), (stirS j k : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ k *
    (C z * c z ^ k * Complex.exp (c z * ((Real.exp t : ℝ) : ℂ)))

lemma hankelH_continuous (C c : ℂ → ℂ) (hC : Continuous C) (hc : Continuous c) (j : ℕ) :
    Continuous (fun p : ℝ × ℂ => hankelH C c j p.1 p.2) := by
  unfold hankelH
  fun_prop

/-- Indicator of the closed ball of radius `R`, applied to the `s`-slice. -/
noncomputable def diskF (R : ℝ) (C c : ℂ → ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  (Metric.closedBall (0 : ℂ) R).indicator
    (fun w => C w * Complex.exp (c w * ((Real.exp s : ℝ) : ℂ))) z

lemma diskF_contDiff (R : ℝ) (C c : ℂ → ℂ) (z : ℂ) :
    ContDiff ℝ ∞ (fun s => diskF R C c s z) := by
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
  · have : (fun s => diskF R C c s z)
        = fun s : ℝ => C z * Complex.exp (c z * ((Real.exp s : ℝ) : ℂ)) := by
      funext s
      unfold diskF
      rw [Set.indicator_of_mem hz]
    rw [this]
    exact contDiff_const.mul (contDiff_const.mul (contDiff_ofReal'.comp Real.contDiff_exp)).cexp
  · have : (fun s => diskF R C c s z) = fun _ : ℝ => (0 : ℂ) := by
      funext s
      unfold diskF
      rw [Set.indicator_of_notMem hz]
    rw [this]
    exact contDiff_const

lemma diskF_formula (R : ℝ) (C c : ℂ → ℂ) (j : ℕ) (t : ℝ) (z : ℂ) :
    iteratedDeriv j (fun s => diskF R C c s z) t
      = (Metric.closedBall (0 : ℂ) R).indicator (fun w => hankelH C c j t w) z := by
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
  · have : (fun s => diskF R C c s z)
        = fun s : ℝ => C z * Complex.exp (c z * ((Real.exp s : ℝ) : ℂ)) := by
      funext s
      unfold diskF
      rw [Set.indicator_of_mem hz]
    rw [this, Set.indicator_of_mem hz]
    exact iteratedDeriv_exp_comp (C z) (c z) j t
  · have : (fun s => diskF R C c s z) = fun _ : ℝ => (0 : ℂ) := by
      funext s
      unfold diskF
      rw [Set.indicator_of_notMem hz]
    rw [this, Set.indicator_of_notMem hz, iteratedDeriv_const]
    simp

/-- Differentiation of `∫_{closedBall 0 R} C(z) exp(c(z) e^s) dz` at `s = 0`. -/
theorem integral_iter_exp (R : ℝ) (C c : ℂ → ℂ) (hC : Continuous C) (hc : Continuous c)
    (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R,
        C z * Complex.exp (c z * ((Real.exp s : ℝ) : ℂ))) 0
      = ∫ z in Metric.closedBall (0 : ℂ) R,
        ∑ k ∈ Finset.range (m + 1), (stirS m k : ℂ) * (C z * c z ^ k * Complex.exp (c z)) := by
  have hSc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hbd : ∀ j : ℕ, ∃ K : ℝ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖hankelH C c j t z‖ ≤ K := by
    intro j
    obtain ⟨K, hK⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hSc).exists_bound_of_continuousOn
      (hankelH_continuous C c hC hc j).continuousOn
    exact ⟨K, fun t ht z hz => hK (t, z) ⟨Metric.ball_subset_closedBall ht, hz⟩⟩
  choose K hK using hbd
  have hmeas : ∀ j ≤ m, ∀ t : ℝ,
      AEStronglyMeasurable (fun z => iteratedDeriv j (fun s => diskF R C c s z) t) volume := by
    intro j _ t
    have hfun : (fun z => iteratedDeriv j (fun s => diskF R C c s z) t)
        = (Metric.closedBall (0 : ℂ) R).indicator (fun z => hankelH C c j t z) :=
      funext fun z => diskF_formula R C c j t z
    rw [hfun]
    have hcont : Continuous (fun z : ℂ => hankelH C c j t z) := by
      unfold hankelH
      fun_prop
    exact hcont.aestronglyMeasurable.indicator measurableSet_closedBall
  have hint : ∀ j ≤ m, Integrable
      (fun z => (Metric.closedBall (0 : ℂ) R).indicator (fun _ => K j) z) volume := by
    intro j _
    exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const hSc.measure_lt_top.ne)
  have hle : ∀ j ≤ m, ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ z : ℂ,
      ‖iteratedDeriv j (fun s => diskF R C c s z) t‖
        ≤ (Metric.closedBall (0 : ℂ) R).indicator (fun _ => K j) z := by
    intro j _ t ht z
    rw [diskF_formula R C c j t z]
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      exact hK j t ht z hz
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      simp
  have key := iteratedDeriv_integral (diskF R C c) (t₀ := 0) (ε := 1) one_pos m
    (fun z => diskF_contDiff R C c z) hmeas
    (fun j z => (Metric.closedBall (0 : ℂ) R).indicator (fun _ => K j) z) hint hle 0
    (Metric.mem_ball_self one_pos)
  have h1 : (fun t : ℝ => ∫ x, diskF R C c t x ∂volume)
      = fun s : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R,
        C z * Complex.exp (c z * ((Real.exp s : ℝ) : ℂ)) := by
    funext s
    exact integral_indicator measurableSet_closedBall
  rw [h1] at key
  rw [key]
  have h2 : (fun x : ℂ => iteratedDeriv m (fun t => diskF R C c t x) 0)
      = fun x => (Metric.closedBall (0 : ℂ) R).indicator (fun z => hankelH C c m 0 z) x :=
    funext fun x => diskF_formula R C c m 0 x
  rw [h2, integral_indicator measurableSet_closedBall]
  refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
  unfold hankelH
  simp

/-- The disk moment of the statement. -/
noncomputable def diskMom (a R : ℝ) (r k l : ℕ) : ℂ :=
  ∫ z in Metric.closedBall (0 : ℂ) R, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
    Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))

noncomputable def cfunH (z : ℂ) : ℂ := (I / 4) * z ^ 4

noncomputable def dfunH (z : ℂ) : ℂ := (I / 4) * (conj z) ^ 4

noncomputable def BpH (a : ℝ) (r p : ℕ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + cfunH z) *
    ∑ k ∈ Finset.range (p + 1), (stirS p k : ℂ) * cfunH z ^ k

lemma cfunH_cont : Continuous cfunH := by
  unfold cfunH; fun_prop

lemma dfunH_cont : Continuous dfunH := by
  unfold dfunH; fun_prop

lemma BpH_cont (a : ℝ) (r p : ℕ) : Continuous (BpH a r p) := by
  have := cfunH_cont
  unfold BpH
  fun_prop

/-- Step A: the `t₁`-derivatives at `0` for fixed `t₂`. -/
lemma stepA (a R : ℝ) (r p : ℕ) (t₂ : ℝ) :
    iteratedDeriv p (fun s : ℝ => diskSource a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ)) 0
      = ∫ z in Metric.closedBall (0 : ℂ) R,
          BpH a r p z * Complex.exp (dfunH z * ((Real.exp t₂ : ℝ) : ℂ)) := by
  have hfun : (fun s : ℝ => diskSource a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ))
      = fun s : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R,
          (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)
            + dfunH z * ((Real.exp t₂ : ℝ) : ℂ))) z
            * Complex.exp (cfunH z * ((Real.exp s : ℝ) : ℂ)) := by
    funext s
    unfold diskSource
    refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
    simp only [dfunH, cfunH]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hC : Continuous (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)
      + dfunH z * ((Real.exp t₂ : ℝ) : ℂ))) := by
    have := dfunH_cont
    fun_prop
  have key := integral_iter_exp R (fun z : ℂ => ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * Complex.exp
    (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + dfunH z * ((Real.exp t₂ : ℝ) : ℂ))) cfunH hC cfunH_cont p
  beta_reduce at key
  rw [hfun, key]
  refine setIntegral_congr_fun measurableSet_closedBall (fun z _ => ?_)
  unfold BpH
  have hexp : Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + dfunH z * ((Real.exp t₂ : ℝ) : ℂ))
      * Complex.exp (cfunH z)
      = Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + cfunH z)
      * Complex.exp (dfunH z * ((Real.exp t₂ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  linear_combination ((stirS p k : ℂ) * ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * cfunH z ^ k) * hexp

lemma iter_add_eq (g : ℝ → ℂ) (p q : ℕ) (x : ℝ) :
    iteratedDeriv (p + q) g x = iteratedDeriv q (iteratedDeriv p g) x := by
  simp only [iteratedDeriv_eq_iterate]
  rw [show p + q = q + p from add_comm p q, Function.iterate_add]
  rfl

lemma G_eq (a R : ℝ) (r : ℕ) (t₁ t₂ : ℝ) :
    diskSource a R r ((Real.exp t₁ : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ)
      = diskSource a R r ((Real.exp (t₁ + t₂) : ℝ) : ℂ) 1 := by
  rw [diskSource_eq_mul a R r (Real.exp t₁) (Real.exp t₂) (Real.exp_pos _) (Real.exp_pos _)]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]

/-- Pointwise expansion of the `t₂`-derivative integrand. -/
lemma pw_identity (a : ℝ) (r p q : ℕ) (z : ℂ) :
    ∑ l ∈ Finset.range (q + 1), (stirS q l : ℂ) *
        (BpH a r p z * dfunH z ^ l * Complex.exp (dfunH z))
      = ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
          (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) *
            (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
              Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))) := by
  have hexp : Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + cfunH z) * Complex.exp (dfunH z)
      = Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold cfunH dfunH
    ring
  have hc : ∀ k : ℕ, cfunH z ^ k = (I / 4) ^ k * z ^ (4 * k) := by
    intro k
    unfold cfunH
    rw [mul_pow, ← pow_mul]
  have hd : ∀ l : ℕ, dfunH z ^ l = (I / 4) ^ l * conj z ^ (4 * l) := by
    intro l
    unfold dfunH
    rw [mul_pow, ← pow_mul]
  unfold BpH
  simp only [hc, hd]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  linear_combination ((stirS q l : ℂ) * (stirS p k : ℂ) * ((‖z‖ ^ (2 * r) : ℝ) : ℂ)
    * (I / 4) ^ k * z ^ (4 * k) * (I / 4) ^ l * conj z ^ (4 * l)) * hexp

/-- The truncated Hankel identity. -/
theorem disk_hankel (a R : ℝ) (r p q : ℕ) :
    ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
      (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) * diskMom a R r k l =
    iteratedDeriv (p + q) (fun t : ℝ => diskSource a R r (Real.exp t : ℂ) 1) 0 := by
  have hL : iteratedDeriv (p + q) (fun t : ℝ => diskSource a R r (Real.exp t : ℂ) 1) 0
      = iteratedDeriv q (fun t₂ : ℝ => iteratedDeriv p
          (fun s : ℝ => diskSource a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ)) 0) 0 := by
    rw [iter_add_eq]
    congr 1
    funext t₂
    have hsh : (fun s : ℝ => diskSource a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ))
        = fun s : ℝ => diskSource a R r ((Real.exp (s + t₂) : ℝ) : ℂ) 1 :=
      funext fun s => G_eq a R r s t₂
    have hc : iteratedDeriv p (fun s : ℝ => diskSource a R r ((Real.exp (s + t₂) : ℝ) : ℂ) 1)
        = fun t : ℝ => iteratedDeriv p (fun t' : ℝ => diskSource a R r (Real.exp t' : ℂ) 1)
            (t + t₂) :=
      iteratedDeriv_comp_add_const p (f := fun t' : ℝ => diskSource a R r (Real.exp t' : ℂ) 1)
        (s := t₂)
    rw [hsh, hc]
    simp
  rw [hL]
  have hfun2 : (fun t₂ : ℝ => iteratedDeriv p
      (fun s : ℝ => diskSource a R r ((Real.exp s : ℝ) : ℂ) ((Real.exp t₂ : ℝ) : ℂ)) 0)
      = fun t₂ : ℝ => ∫ z in Metric.closedBall (0 : ℂ) R,
          BpH a r p z * Complex.exp (dfunH z * ((Real.exp t₂ : ℝ) : ℂ)) :=
    funext fun t₂ => stepA a R r p t₂
  rw [hfun2]
  have hB := integral_iter_exp R (BpH a r p) dfunH (BpH_cont a r p) dfunH_cont q
  beta_reduce at hB
  rw [hB]
  have hSc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hint : ∀ k ∈ Finset.range (p + 1), ∀ l ∈ Finset.range (q + 1),
      Integrable (fun z : ℂ => (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) *
            (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
              Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))))
        (volume.restrict (Metric.closedBall (0 : ℂ) R)) := by
    intro k _ l _
    have hcont : Continuous (fun z : ℂ => (stirS p k : ℂ) * (stirS q l : ℂ) * (I / 4) ^ (k + l) *
            (((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (4 * k) * conj z ^ (4 * l) *
              Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4)))) := by
      fun_prop
    exact hcont.continuousOn.integrableOn_compact hSc
  symm
  rw [setIntegral_congr_fun measurableSet_closedBall (fun z _ => pw_identity a r p q z)]
  rw [integral_finsetSum (Finset.range (p + 1)) (fun k hk =>
    integrable_finsetSum (Finset.range (q + 1)) (fun l hl => hint k hk l hl))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [integral_finsetSum (Finset.range (q + 1)) (fun l hl => hint k hk l hl)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [integral_const_mul]
  rfl

end Painleve
