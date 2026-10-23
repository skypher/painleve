import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Statement of the main theorem

Frozen Lean statement of Theorem 1.1 of `paper.tex` (labels `thm:main`,
`sec:gram`, `eq:density`, `eq:pairing`, `eq:rho-sign`, `eq:signed-norm`,
`eq:quartic-recurrence`, `eq:initial-values`, `eq:h-bessel`).

The Hermitian form is that of Felder–Hoppe, SIGMA 21 (2025) 103,
Proposition 3.1, for `d = 4`, with the right inverse `χ(r) = r`.
-/

open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

/-- The quartic density `ρ_a(z) = exp(-a|z|² + (i/4)(z⁴ + z̄⁴))` (`eq:density`). -/
noncomputable def density (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / 4) * (z ^ 4 + conj z ^ 4))

/-- `η = e^{πi/4}`. -/
noncomputable def eta : ℂ := Complex.exp (↑Real.pi * I / 4)

/-- The twist `σ`: on the weight space `𝒫_r` it is `f ↦ (-η)^{-r} f(η z)`; on a
monomial `z^m` with `m ≡ r (mod 4)`, `0 ≤ r ≤ 3`, it multiplies by
`(-η)^{-r} η^m` (Felder–Hoppe, Proposition 3.1, `χ(r) = r`). -/
noncomputable def twist (f : ℂ[X]) : ℂ[X] :=
  f.sum fun m c => monomial m (c * (-eta) ^ (-((m % 4 : ℕ) : ℤ)) * eta ^ m)

/-- The pairing `(f, g)_a = ∫ f(z) conj(σ g(z)) ρ_a(z) dA(z)` (`eq:pairing`). -/
noncomputable def pairing (a : ℝ) (f g : ℂ[X]) : ℂ :=
  ∫ z : ℂ, f.eval z * conj ((twist g).eval z) * density a z

/-- The leading `n × n` Gram matrix `[(z^p, z^q)_a]_{p,q=0}^{n-1}`. -/
noncomputable def gramLead (a : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun p q => pairing a (X ^ (p : ℕ)) (X ^ (q : ℕ))

/-- Felder–Hoppe's sign `τ(ℓ)` (Lemma 3.4, `d = 4`). -/
def tau (l : ℕ) : ℝ := if l % 4 = 3 then -1 else 1

/-- Felder–Hoppe's sign `ϱ(n) = (-1)^n ∏_{ℓ<n} τ(ℓ)` (Example 3.5, `eq:rho-sign`). -/
def rhoSign (n : ℕ) : ℝ := (-1) ^ n * ∏ l ∈ Finset.range n, tau l

/-- The signed norm `𝔥_n`, written through the leading Gram determinants:
`𝔥_n = ϱ(n) · det G_{n+1} / det G_n`. Part (i) of `Stmt_main` states that this
is the signed norm of the monic orthogonal polynomial of degree `n`
(`eq:signed-norm`). -/
noncomputable def signedNorm (a : ℝ) (n : ℕ) : ℝ :=
  rhoSign n * ((gramLead a (n + 1)).det / (gramLead a n).det).re

/-- The Bessel function `J_ν(x) = Σ_k (-1)^k (x/2)^{2k+ν} / (k! Γ(k+ν+1))`
for `x > 0` (DLMF 10.2.2). -/
noncomputable def besselJ (ν x : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k / ((k.factorial : ℝ) * Real.Gamma (k + ν + 1)) *
    (x / 2) ^ (2 * (k : ℝ) + ν)

/-- The initial function `h(a)` of `eq:h-bessel`. -/
noncomputable def hBessel (a : ℝ) : ℝ :=
  Real.pi ^ 2 * a / 4 *
    (besselJ (-1 / 4) (a ^ 2 / 4) ^ 2
      - Real.sqrt 2 * besselJ (-1 / 4) (a ^ 2 / 4) * besselJ (1 / 4) (a ^ 2 / 4)
      + besselJ (1 / 4) (a ^ 2 / 4) ^ 2)

/-- `v_0 = -h'(a) / (a h(a))` (`eq:initial-values`). -/
noncomputable def v0 (a : ℝ) : ℝ := -deriv hBessel a / (a * hBessel a)

/-- `v_1 = -h''(a) / (a h'(a))` (`eq:initial-values`). -/
noncomputable def v1 (a : ℝ) : ℝ := -deriv (deriv hBessel) a / (a * deriv hBessel a)

/-- Extension by zero to negative indices. -/
def extZ (v : ℕ → ℝ) (k : ℤ) : ℝ := if k < 0 then 0 else v k.toNat

/-- The quartic recurrence `eq:quartic-recurrence` with `ε = a⁻²` and
`v_n = 0` for `n < 0`. -/
def QuarticRec (a : ℝ) (v : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    v n * (1 + extZ v ((n : ℤ) - 1) * extZ v ((n : ℤ) - 2)
        + v (n + 1) * extZ v ((n : ℤ) - 1) + v (n + 2) * v (n + 1))
      = ((n : ℝ) + 1) / a ^ 2

/-- Solutions of the recurrence with the prescribed initial values. -/
def IsSolution (a : ℝ) (v : ℕ → ℝ) : Prop :=
  v 0 = v0 a ∧ v 1 = v1 a ∧ QuarticRec a v

/-- **Theorem 1.1** (`thm:main`).

(i) For `a > 0` every leading Gram matrix is nondegenerate (Felder–Hoppe
Conjecture 3.6 for `d = 4`, `a > 0`); for every `n` there is a unique monic
polynomial of degree `n` orthogonal to `1, z, …, z^{n-1}`, its square norm is
`ϱ(n) 𝔥_n`, and `𝔥_n > 0`.

(ii) `h(a) ≠ 0` and `h'(a) ≠ 0`, so the initial values are defined; they
extend uniquely to a real solution of the recurrence, and that solution is
`v_n = 𝔥_{n+1} / (a 𝔥_n) > 0`. -/
def Stmt_main : Prop :=
  ∀ a : ℝ, 0 < a →
    ((∀ n : ℕ, (gramLead a n).det ≠ 0) ∧
      ∀ n : ℕ, 0 < signedNorm a n ∧
        (∃! P : ℂ[X], P.Monic ∧ P.natDegree = n ∧ ∀ j < n, pairing a P (X ^ j) = 0) ∧
        ∀ P : ℂ[X], P.Monic → P.natDegree = n → (∀ j < n, pairing a P (X ^ j) = 0) →
          pairing a P P = ((rhoSign n * signedNorm a n : ℝ) : ℂ)) ∧
    (hBessel a ≠ 0 ∧ deriv hBessel a ≠ 0 ∧
      (∃! v : ℕ → ℝ, IsSolution a v) ∧
      ∀ v : ℕ → ℝ, IsSolution a v →
        ∀ n : ℕ, 0 < v n ∧ v n = signedNorm a (n + 1) / (a * signedNorm a n))

end Painleve
