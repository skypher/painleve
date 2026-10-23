import Painleve.Statement
import Painleve.Signs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic

/-!
# The quartic recurrence from the Hermitian form (Section 5 of `paper.tex`)

We work with an abstract form `B` on `ℂ[X]` that is linear in the first
argument, Hermitian, orthogonal across `C₄`-weights, and satisfies the
integration by parts `(L f, z^q) = -τ(q) a (f, z^{q+1})` with
`L = ∂_z + i z³` (`eq:ibp-pairing`). Given monic orthogonal polynomials with
signed norms `ϱ(n) 𝔥_n`, `𝔥_n > 0`, the ratios `v_n = 𝔥_{n+1}/(a 𝔥_n)` solve
`eq:quartic-recurrence`.
-/

open Polynomial Finset
open scoped ComplexConjugate

namespace Painleve

/-- Hypotheses on the form, Section 5. -/
structure FormHyp (B : ℂ[X] → ℂ[X] → ℂ) (a : ℝ) : Prop where
  add_left : ∀ f g k, B (f + g) k = B f k + B g k
  smul_left : ∀ (c : ℂ) f k, B (C c * f) k = c * B f k
  herm : ∀ f g, B f g = conj (B g f)
  weight : ∀ p q : ℕ, p % 4 ≠ q % 4 → B (X ^ p) (X ^ q) = 0
  ibp : ∀ (f : ℂ[X]) (q : ℕ),
    B (derivative f + C Complex.I * X ^ 3 * f) (X ^ q) = -(tau q : ℂ) * a * B f (X ^ (q + 1))

/-- Monic orthogonal polynomials with positive signed norms. -/
structure OPData (B : ℂ[X] → ℂ[X] → ℂ) where
  P : ℕ → ℂ[X]
  h : ℕ → ℝ
  monic : ∀ n, (P n).Monic
  deg : ∀ n, (P n).natDegree = n
  orth : ∀ n, ∀ j < n, B (P n) (X ^ j) = 0
  norm : ∀ n, B (P n) (P n) = ((rhoSign n * h n : ℝ) : ℂ)
  pos : ∀ n, 0 < h n

variable {B : ℂ[X] → ℂ[X] → ℂ} {a : ℝ}

namespace FormHyp

variable (hB : FormHyp B a)
include hB

theorem zero_left (k : ℂ[X]) : B 0 k = 0 := by
  have := hB.add_left 0 0 k
  simp only [add_zero] at this
  linear_combination -this

theorem neg_left (f k : ℂ[X]) : B (-f) k = -B f k := by
  have := hB.smul_left (-1) f k
  simpa using this

theorem sub_left (f g k : ℂ[X]) : B (f - g) k = B f k - B g k := by
  rw [sub_eq_add_neg, hB.add_left, hB.neg_left, ← sub_eq_add_neg]

theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (k : ℂ[X]) :
    B (∑ i ∈ s, f i) k = ∑ i ∈ s, B (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB.zero_left]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, hB.add_left, ih]

theorem add_right (f g k : ℂ[X]) : B k (f + g) = B k f + B k g := by
  rw [hB.herm, hB.add_left, map_add, ← hB.herm, ← hB.herm]

theorem smul_right (c : ℂ) (f k : ℂ[X]) : B k (C c * f) = conj c * B k f := by
  rw [hB.herm, hB.smul_left, map_mul, ← hB.herm]

theorem zero_right (k : ℂ[X]) : B k 0 = 0 := by
  rw [hB.herm, hB.zero_left, map_zero]

theorem sub_right (f g k : ℂ[X]) : B k (f - g) = B k f - B k g := by
  rw [hB.herm, hB.sub_left, map_sub, ← hB.herm, ← hB.herm]

theorem sum_right {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (k : ℂ[X]) :
    B k (∑ i ∈ s, f i) = ∑ i ∈ s, B k (f i) := by
  rw [hB.herm, hB.sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hB.herm _ _).symm

theorem expand_left (f k : ℂ[X]) (N : ℕ) (hN : f.natDegree < N) :
    B f k = ∑ i ∈ range N, f.coeff i * B (X ^ i) k := by
  conv_lhs => rw [as_sum_range' f N hN]
  rw [hB.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← C_mul_X_pow_eq_monomial, hB.smul_left]

theorem expand_right (f k : ℂ[X]) (N : ℕ) (hN : f.natDegree < N) :
    B k f = ∑ i ∈ range N, conj (f.coeff i) * B k (X ^ i) := by
  conv_lhs => rw [as_sum_range' f N hN]
  rw [hB.sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← C_mul_X_pow_eq_monomial, hB.smul_right]

end FormHyp

end Painleve
