import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace Painleve

open scoped ContDiff
open Finset

/-- Stirling numbers of the second kind. -/
def stirS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | q + 1, j + 1 => (j + 1) * stirS q (j + 1) + stirS q j

lemma stirS_succ_zero (q : ℕ) : stirS (q + 1) 0 = 0 := rfl

lemma stirS_succ_succ (q j : ℕ) :
    stirS (q + 1) (j + 1) = (j + 1) * stirS q (j + 1) + stirS q j := rfl

lemma stirS_eq_zero_aux : ∀ q j : ℕ, q < j → stirS q j = 0 := by
  intro q
  induction q with
  | zero =>
    intro j h
    cases j with
    | zero => omega
    | succ j => rfl
  | succ q ih =>
    intro j h
    cases j with
    | zero => omega
    | succ j =>
      rw [stirS_succ_succ, ih (j + 1) (by omega), ih j (by omega)]
      simp

theorem stirS_self (q : ℕ) : stirS q q = 1 := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [stirS_succ_succ, ih, stirS_eq_zero_aux q (q + 1) (by omega)]
    simp

theorem stirS_eq_zero_of_lt {q j : ℕ} (h : q < j) : stirS q j = 0 :=
  stirS_eq_zero_aux q j h

/-- Combinatorial identity behind the induction for `iteratedDeriv_comp_exp`. -/
lemma sum_identity (q : ℕ) (T : ℕ → ℂ) :
    ∑ j ∈ range (q + 1 + 1), (stirS (q + 1) j : ℂ) * T j
      = ∑ j ∈ range (q + 1), (stirS q j : ℂ) * ((j : ℂ) * T j + T (j + 1)) := by
  have hA : ∑ j ∈ range (q + 1), (stirS q j : ℂ) * ((j : ℂ) * T j)
      = ∑ j ∈ range (q + 1), ((j : ℂ) + 1) * (stirS q (j + 1) : ℂ) * T (j + 1) := by
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs => rw [Finset.sum_range_succ]
    rw [stirS_eq_zero_of_lt (show q < q + 1 by omega)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hB : ∑ j ∈ range (q + 1), (stirS q j : ℂ) * ((j : ℂ) * T j + T (j + 1))
      = ∑ j ∈ range (q + 1), (stirS q j : ℂ) * ((j : ℂ) * T j)
        + ∑ j ∈ range (q + 1), (stirS q j : ℂ) * T (j + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hB, hA, ← Finset.sum_add_distrib, Finset.sum_range_succ']
  simp only [stirS_succ_zero, stirS_succ_succ, Nat.cast_zero, zero_mul, add_zero, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma iter_smooth (Φ : ℝ → ℂ) (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ioi 0)) (j : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv j Φ) (Set.Ioi 0) := by
  induction j with
  | zero => rw [iteratedDeriv_zero]; exact hΦ
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

lemma iter_hasDerivAt (Φ : ℝ → ℂ) (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ioi 0)) (j : ℕ) (x : ℝ)
    (hx : 0 < x) : HasDerivAt (iteratedDeriv j Φ) (iteratedDeriv (j + 1) Φ x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j Φ) x :=
    ((iter_smooth Φ hΦ j).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- Derivative of `s ↦ f(s)^j * Φ^{(j)}(f(s))` along a real map `f` with `f' = c f`. -/
lemma hasDerivAt_term (Φ : ℝ → ℂ) (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ioi 0)) (j : ℕ)
    (f : ℝ → ℝ) (c t : ℝ) (hf : HasDerivAt f (c * f t) t) (hpos : 0 < f t) :
    HasDerivAt (fun s => ((f s : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (f s))
      ((j : ℂ) * (c : ℂ) * ((f t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (f t)
        + ((f t : ℝ) : ℂ) ^ j * (iteratedDeriv (j + 1) Φ (f t) * ((c * f t : ℝ) : ℂ))) t := by
  have hD : HasDerivAt (fun s => iteratedDeriv j Φ (f s))
      (iteratedDeriv (j + 1) Φ (f t) * ((c * f t : ℝ) : ℂ)) t := by
    have h1 := (iter_hasDerivAt Φ hΦ j (f t) hpos).scomp t hf
    refine h1.congr_deriv ?_
    rw [Complex.real_smul]
    ring
  have hF : HasDerivAt (fun s => ((f s : ℝ) : ℂ)) ((c * f t : ℝ) : ℂ) t := hf.ofReal_comp
  have hP := hF.pow j
  have key : (j : ℂ) * ((f t : ℝ) : ℂ) ^ (j - 1) * ((c * f t : ℝ) : ℂ)
      = (j : ℂ) * (c : ℂ) * ((f t : ℝ) : ℂ) ^ j := by
    push_cast
    cases j with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have hM := hP.mul hD
  refine hM.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [key]

theorem iteratedDeriv_comp_exp (Φ : ℝ → ℂ) (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ioi 0)) (q : ℕ) (t : ℝ) :
    iteratedDeriv q (fun t => Φ (Real.exp t)) t =
      ∑ j ∈ Finset.range (q + 1),
        (stirS q j : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t) := by
  have hall : ∀ q : ℕ, iteratedDeriv q (fun t => Φ (Real.exp t)) =
      fun t => ∑ j ∈ Finset.range (q + 1),
        (stirS q j : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t) := by
    intro q
    induction q with
    | zero =>
      funext t
      simp [stirS, iteratedDeriv_zero]
    | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      apply HasDerivAt.deriv
      have hterm : ∀ j ∈ Finset.range (q + 1),
          HasDerivAt (fun s => (stirS q j : ℂ) * (((Real.exp s : ℝ) : ℂ) ^ j
              * iteratedDeriv j Φ (Real.exp s)))
            ((stirS q j : ℂ) * ((j : ℂ) * (((Real.exp t : ℝ) : ℂ) ^ j
              * iteratedDeriv j Φ (Real.exp t))
              + ((Real.exp t : ℝ) : ℂ) ^ (j + 1) * iteratedDeriv (j + 1) Φ (Real.exp t))) t := by
        intro j _
        have h := (hasDerivAt_term Φ hΦ j Real.exp 1 t
          (by simpa using Real.hasDerivAt_exp t) (Real.exp_pos t)).const_mul (stirS q j : ℂ)
        refine h.congr_deriv ?_
        push_cast
        ring
      have hsum := HasDerivAt.fun_sum hterm
      have hfunEq : (fun t : ℝ => ∑ j ∈ Finset.range (q + 1),
          (stirS q j : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t))
          = (fun t : ℝ => ∑ j ∈ Finset.range (q + 1),
          (stirS q j : ℂ) * (((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t))) := by
        funext t
        simp only [mul_assoc]
      have hval : ∑ j ∈ Finset.range (q + 1 + 1),
          (stirS (q + 1) j : ℂ) * ((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t)
          = ∑ j ∈ Finset.range (q + 1),
          (stirS q j : ℂ) * ((j : ℂ) * (((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t))
            + ((Real.exp t : ℝ) : ℂ) ^ (j + 1) * iteratedDeriv (j + 1) Φ (Real.exp t)) := by
        simp only [mul_assoc]
        exact sum_identity q (fun j => ((Real.exp t : ℝ) : ℂ) ^ j * iteratedDeriv j Φ (Real.exp t))
      rw [hfunEq, hval]
      exact hsum
  exact congrFun (hall q) t

/-- Coefficients of the scaling derivative. -/
noncomputable def kappa (γ : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | p + 1, 0 => (-γ) * kappa γ p 0
  | p + 1, i + 1 => (-γ - ((i : ℝ) + 1) / 2) * kappa γ p (i + 1) - (1 / 2) * kappa γ p i

lemma kappa_succ_zero (γ : ℝ) (p : ℕ) : kappa γ (p + 1) 0 = (-γ) * kappa γ p 0 := rfl

lemma kappa_succ_succ (γ : ℝ) (p i : ℕ) :
    kappa γ (p + 1) (i + 1) = (-γ - ((i : ℝ) + 1) / 2) * kappa γ p (i + 1)
      - (1 / 2) * kappa γ p i := rfl

lemma kappa_eq_zero_aux (γ : ℝ) : ∀ p i : ℕ, p < i → kappa γ p i = 0 := by
  intro p
  induction p with
  | zero =>
    intro i h
    cases i with
    | zero => omega
    | succ i => rfl
  | succ p ih =>
    intro i h
    cases i with
    | zero => omega
    | succ i =>
      rw [kappa_succ_succ, ih (i + 1) (by omega), ih i (by omega)]
      ring

theorem kappa_self (γ : ℝ) (p : ℕ) : kappa γ p p = (-1 / 2) ^ p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [kappa_succ_succ, ih, kappa_eq_zero_aux γ p (p + 1) (by omega)]
    rw [pow_succ]
    ring

theorem kappa_eq_zero_of_lt (γ : ℝ) {p i : ℕ} (h : p < i) : kappa γ p i = 0 :=
  kappa_eq_zero_aux γ p i h

lemma sum_shift (F : ℕ → ℂ) (p : ℕ) (hF : F (p + 1) = 0) :
    ∑ i ∈ range (p + 1), F (i + 1) + F 0 = ∑ i ∈ range (p + 1), F i := by
  have h1 := Finset.sum_range_succ' F (p + 1)
  have h2 := Finset.sum_range_succ F (p + 1)
  rw [hF, add_zero] at h2
  rw [h2] at h1
  exact h1.symm

/-- The `kappa` recurrence, in the form used for the induction. -/
lemma kappa_sum (γ : ℝ) (p : ℕ) (A : ℕ → ℂ) :
    ∑ i ∈ range (p + 1 + 1), ((kappa γ (p + 1) i : ℝ) : ℂ) * A i
      = ∑ i ∈ range (p + 1), ((kappa γ p i : ℝ) : ℂ) * ((-(γ : ℂ)) - (i : ℂ) / 2) * A i
        - ∑ i ∈ range (p + 1), ((kappa γ p i : ℝ) : ℂ) * (1 / 2) * A (i + 1) := by
  have hsh := sum_shift (fun i => ((kappa γ p i : ℝ) : ℂ) * ((-(γ : ℂ)) - (i : ℂ) / 2) * A i) p
    (by
      simp only [kappa_eq_zero_aux γ p (p + 1) (Nat.lt_succ_self p), Complex.ofReal_zero,
        zero_mul])
  rw [Finset.sum_range_succ']
  have hpt : ∀ i ∈ range (p + 1), ((kappa γ (p + 1) (i + 1) : ℝ) : ℂ) * A (i + 1)
      = ((kappa γ p (i + 1) : ℝ) : ℂ) * ((-(γ : ℂ)) - ((i + 1 : ℕ) : ℂ) / 2) * A (i + 1)
        - ((kappa γ p i : ℝ) : ℂ) * (1 / 2) * A (i + 1) := by
    intro i _
    rw [kappa_succ_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, kappa_succ_zero]
  beta_reduce at hsh
  push_cast at hsh ⊢
  linear_combination hsh

theorem iteratedDeriv_scaling (g : ℝ → ℂ) (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0))
    (γ y : ℝ) (hy : 0 < y) (p : ℕ) (t : ℝ) :
    iteratedDeriv p (fun t => ((Real.exp (-γ * t) : ℝ) : ℂ) * g (y * Real.exp (-t / 2))) t =
      ((Real.exp (-γ * t) : ℝ) : ℂ) * ∑ i ∈ Finset.range (p + 1),
        (kappa γ p i : ℂ) * (((y * Real.exp (-t / 2)) : ℝ) : ℂ) ^ i *
          iteratedDeriv i g (y * Real.exp (-t / 2)) := by
  have hall : ∀ p : ℕ,
      iteratedDeriv p (fun t => ((Real.exp (-γ * t) : ℝ) : ℂ) * g (y * Real.exp (-t / 2)))
        = fun t => ((Real.exp (-γ * t) : ℝ) : ℂ) * ∑ i ∈ Finset.range (p + 1),
          (kappa γ p i : ℂ) * ((((y * Real.exp (-t / 2)) : ℝ) : ℂ) ^ i
            * iteratedDeriv i g (y * Real.exp (-t / 2))) := by
    intro p
    induction p with
    | zero =>
      funext t
      simp [kappa, iteratedDeriv_zero]
    | succ p ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      apply HasDerivAt.deriv
      have hE : HasDerivAt (fun s : ℝ => ((Real.exp (-γ * s) : ℝ) : ℂ))
          (((Real.exp (-γ * t) * (-γ) : ℝ)) : ℂ) t := by
        have h : HasDerivAt (fun s : ℝ => Real.exp (-γ * s))
            (Real.exp (-γ * t) * (-γ)) t := by
          refine (((hasDerivAt_id' t).const_mul (-γ)).exp).congr_deriv ?_
          ring
        exact h.ofReal_comp
      have hf : HasDerivAt (fun s : ℝ => y * Real.exp (-s / 2))
          (-1 / 2 * (y * Real.exp (-t / 2))) t := by
        refine ((((hasDerivAt_id' t).neg.div_const 2).exp).const_mul y).congr_deriv ?_
        simp only [Pi.neg_apply]
        ring_nf
      have hpos : 0 < y * Real.exp (-t / 2) := mul_pos hy (Real.exp_pos _)
      have hT : ∀ i ∈ Finset.range (p + 1),
          HasDerivAt (fun s : ℝ => (kappa γ p i : ℂ)
              * ((((y * Real.exp (-s / 2)) : ℝ) : ℂ) ^ i * iteratedDeriv i g (y * Real.exp (-s / 2))))
            ((kappa γ p i : ℂ) * (-(1 / 2 : ℂ) * ((i : ℂ)
              * ((((y * Real.exp (-t / 2)) : ℝ) : ℂ) ^ i * iteratedDeriv i g (y * Real.exp (-t / 2)))
              + ((((y * Real.exp (-t / 2)) : ℝ) : ℂ) ^ (i + 1)
                * iteratedDeriv (i + 1) g (y * Real.exp (-t / 2)))))) t := by
        intro i _
        have h := (hasDerivAt_term g hg i (fun s => y * Real.exp (-s / 2)) (-1 / 2) t hf hpos).const_mul
          (kappa γ p i : ℂ)
        refine h.congr_deriv ?_
        push_cast
        ring
      have hsum := HasDerivAt.fun_sum hT
      have hprod := hE.mul hsum
      refine hprod.congr_deriv ?_
      have hK := kappa_sum γ p (fun i => ((((y * Real.exp (-t / 2)) : ℝ) : ℂ) ^ i
        * iteratedDeriv i g (y * Real.exp (-t / 2))))
      beta_reduce at hK
      rw [hK]
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
  have := congrFun (hall p) t
  rw [this]
  simp only [mul_assoc]

end Painleve
