import Painleve.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Statements of the general-`d` results

Frozen Lean statements of Theorem 1.1, Theorem 1.3 and Corollary 4.2 of
`paper.tex` (release `v2.2`): labels `thm:main`, `thm:unique`,
`cor:endpoint`, with the definitions of Section 2 (`sec:gram`:
`eq:density`, `eq:pairing`, `eq:twist-sign`, `eq:gram-block`,
`eq:rho-sign`, `eq:signed-norm`), the recurrence `eq:FH-recurrence` with
initial values `eq:FH-initial`, and the normalized recurrence
`eq:general-recurrence`.

The Hermitian form is that of Felder–Hoppe, SIGMA 21 (2025) 103,
Proposition 3.1, for a general degree `d`, with the right inverse
`χ(r) = r`. For `d = 4` the objects below agree with those of
`Painleve/Statement.lean`.
-/

open Complex Polynomial MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Painleve

/-- The density `ρ_a(z) = exp(-a|z|² + (i/d)(z^d + z̄^d))` (`eq:density`). -/
noncomputable def densityD (d : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (I / d) * (z ^ d + conj z ^ d))

/-- `η = e^{πi/d}`. -/
noncomputable def etaD (d : ℕ) : ℂ := Complex.exp (↑Real.pi * I / d)

/-- The twist `σ`: on the weight space `𝒫_r` it is `f ↦ (-η)^{-r} f(η z)`; on a
monomial `z^m` with `m ≡ r (mod d)`, `0 ≤ r ≤ d - 1`, it multiplies by
`(-η)^{-r} η^m` (Felder–Hoppe, Proposition 3.1, `χ(r) = r`). -/
noncomputable def twistD (d : ℕ) (f : ℂ[X]) : ℂ[X] :=
  f.sum fun m c => monomial m (c * (-etaD d) ^ (-((m % d : ℕ) : ℤ)) * etaD d ^ m)

/-- The pairing `(f, g)_a = ∫ f(z) conj(σ g(z)) ρ_a(z) dA(z)` (`eq:pairing`). -/
noncomputable def pairingD (d : ℕ) (a : ℝ) (f g : ℂ[X]) : ℂ :=
  ∫ z : ℂ, f.eval z * conj ((twistD d g).eval z) * densityD d a z

/-- The leading `n × n` Gram matrix `[(z^p, z^q)_a]_{p,q=0}^{n-1}`. -/
noncomputable def gramLeadD (d : ℕ) (a : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun p q => pairingD d a (X ^ (p : ℕ)) (X ^ (q : ℕ))

/-- Felder–Hoppe's sign `τ(ℓ)`: `(-1)^{d-1}` if `ℓ ≡ -1 (mod d)`, else `1`
(Lemma 3.4, `eq:rho-sign`). -/
def tauD (d l : ℕ) : ℝ := if l % d = d - 1 then (-1) ^ (d - 1) else 1

/-- Felder–Hoppe's sign `ϱ(n) = (-1)^n ∏_{ℓ<n} τ(ℓ)` (Example 3.5, `eq:rho-sign`). -/
def rhoSignD (d n : ℕ) : ℝ := (-1) ^ n * ∏ l ∈ Finset.range n, tauD d l

/-- The signed norm `𝔥_n`, written through the leading Gram determinants:
`𝔥_n = ϱ(n) · det G_{n+1} / det G_n`. Part (i) of `Stmt_mainD` states that
this is the signed norm of the monic orthogonal polynomial of degree `n`
(`eq:signed-norm`). -/
noncomputable def signedNormD (d : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  rhoSignD d n * ((gramLeadD d a (n + 1)).det / (gramLeadD d a n).det).re

/-- The planar moment `∫ |z|^{2j} ρ_a(z) dA(z)` (`eq:FH-initial`). -/
noncomputable def momentD (d : ℕ) (a : ℝ) (j : ℕ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * j) : ℝ) : ℂ) * densityD d a z

/-- The Felder–Hoppe recurrence `eq:FH-recurrence`,
`V_n + a⁻² ∑_{j=0}^{d-2} ∏_{k=0}^{d-2} V_{n+j-k} = (n+1)/a`, with `V_n = 0`
for `n < 0`. -/
def FHRec (d : ℕ) (a : ℝ) (V : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    V n + 1 / a ^ 2 * ∑ j ∈ Finset.range (d - 1), ∏ k ∈ Finset.range (d - 1),
        extZ V ((n : ℤ) + j - k)
      = ((n : ℝ) + 1) / a

/-- Solutions of `eq:FH-recurrence` with the initial values `eq:FH-initial`,
`V_j = ∫|z|^{2j+2}ρ_a / ∫|z|^{2j}ρ_a` for `0 ≤ j ≤ d - 3`. -/
def IsSolD (d : ℕ) (a : ℝ) (V : ℕ → ℝ) : Prop :=
  (∀ j < d - 2, ((V j : ℝ) : ℂ) = momentD d a (j + 1) / momentD d a j) ∧ FHRec d a V

/-- **Theorem 1.1** (`thm:main`), all `d ≥ 2`.

(i) For `a > 0` every leading Gram matrix is nondegenerate (Felder–Hoppe
Conjecture 3.6 for `a > 0`); for every `n` there is a unique monic polynomial
of degree `n` orthogonal to `1, z, …, z^{n-1}`, its square norm is
`ϱ(n) 𝔥_n`, and `𝔥_n > 0`.

(ii) For `d ≥ 3` the moments in the initial values are nonzero, the initial
values extend uniquely to a real solution of the recurrence, and that solution
is `V_n = 𝔥_{n+1} / 𝔥_n > 0`.

Demand sheet (paper lines 220–233):
- `d`: every natural `d ≥ 2` for (i), `d ≥ 3` for (ii) (paper: "Let `d ≥ 2`",
  "(ii) Let `d ≥ 3`").
- `a`: every real `a > 0`, chosen after `d`.
- nondegeneracy: `det ≠ 0` for every size `n`, including `n = 0`.
- signed norms: strict positivity for every `n`; identification with the
  square norm of every monic orthogonal polynomial of degree `n`, whose
  existence and uniqueness are asserted.
- (ii) uniqueness among all real sequences (no positivity assumed), existence,
  positivity and the identification `V_n = 𝔥_{n+1}/𝔥_n` for every `n`;
  nonvanishing of the moments that occur as denominators (`j ≤ d - 3`). -/
def Stmt_mainD : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a : ℝ, 0 < a →
    ((∀ n : ℕ, (gramLeadD d a n).det ≠ 0) ∧
      ∀ n : ℕ, 0 < signedNormD d a n ∧
        (∃! P : ℂ[X], P.Monic ∧ P.natDegree = n ∧ ∀ j < n, pairingD d a P (X ^ j) = 0) ∧
        ∀ P : ℂ[X], P.Monic → P.natDegree = n → (∀ j < n, pairingD d a P (X ^ j) = 0) →
          pairingD d a P P = ((rhoSignD d n * signedNormD d a n : ℝ) : ℂ)) ∧
    (3 ≤ d →
      (∀ j < d - 2, momentD d a j ≠ 0) ∧
      (∃! V : ℕ → ℝ, IsSolD d a V) ∧
      ∀ V : ℕ → ℝ, IsSolD d a V →
        ∀ n : ℕ, 0 < V n ∧ V n = signedNormD d a (n + 1) / signedNormD d a n)

/-- The normalized recurrence `eq:general-recurrence`,
`v_n + ∑_{m=n-d+2}^{n} v_m v_{m+1} ⋯ v_{m+d-2} = (n+1) ε`, with `v_n = 0` for
`n < 0`; the window starting at `m = n - j` is `∏_{i=0}^{d-2} v_{n-j+i}`. -/
def GenRec (d : ℕ) (ε : ℝ) (v : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    v n + ∑ j ∈ Finset.range (d - 1), ∏ i ∈ Finset.range (d - 1),
        extZ v ((n : ℤ) - j + i)
      = ((n : ℝ) + 1) * ε

/-- **Theorem 1.3** (`thm:unique`).

For `d ≥ 3` and `ε > 0`, every positive solution of `eq:general-recurrence`
satisfies `v_n ((d-1)/(ε(n+1)))^{1/(d-1)} → 1`, and there is at most one
positive solution. Consequently, for `a > 0`, the sequence `V_n = 𝔥_{n+1}/𝔥_n`
of Theorem 1.1(ii) is the unique positive solution of `eq:FH-recurrence`, and
for `d = 4` the sequence of Theorem 1.2 (Bessel initial values) is the unique
positive solution of `eq:quartic-recurrence`.

Demand sheet (paper lines 298–310):
- `d ≥ 3`, `ε > 0` arbitrary, chosen before the sequences.
- asymptotics: an operational limit (`Tendsto … atTop (𝓝 1)`) for every
  positive solution; no initial values assumed.
- uniqueness: any two positive solutions are equal as functions on `ℕ`.
- consequences: for every `a > 0`, `V_n = 𝔥_{n+1}/𝔥_n` is a positive solution
  of `eq:FH-recurrence` and every positive solution equals it; for `d = 4`,
  there is a positive solution with the Bessel initial values (`IsSolution`)
  and every positive solution of the quartic recurrence equals it. -/
def Stmt_uniqueD : Prop :=
  (∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, 0 < ε →
    (∀ v : ℕ → ℝ, (∀ n, 0 < v n) → GenRec d ε v →
      Tendsto (fun n : ℕ =>
          v n * (((d : ℝ) - 1) / (ε * ((n : ℝ) + 1))) ^ (1 / ((d : ℝ) - 1)))
        atTop (𝓝 1)) ∧
    ∀ v w : ℕ → ℝ, (∀ n, 0 < v n) → (∀ n, 0 < w n) →
      GenRec d ε v → GenRec d ε w → v = w) ∧
  (∀ d : ℕ, 3 ≤ d → ∀ a : ℝ, 0 < a →
    let V : ℕ → ℝ := fun n => signedNormD d a (n + 1) / signedNormD d a n
    (∀ n : ℕ, 0 < V n) ∧ FHRec d a V ∧
      ∀ W : ℕ → ℝ, (∀ n, 0 < W n) → FHRec d a W → W = V) ∧
  (∀ a : ℝ, 0 < a →
    ∃ v : ℕ → ℝ, IsSolution a v ∧ (∀ n : ℕ, 0 < v n) ∧
      ∀ w : ℕ → ℝ, (∀ n, 0 < w n) → QuarticRec a w → w = v)

/-- The index `j_r = min J_r`, where `J_r = {0, …, d-1} \ {d-1-r}`: it is `1`
for `r = d - 1` and `0` otherwise (`cor:endpoint`). -/
def jMin (d r : ℕ) : ℕ := if r = d - 1 then 1 else 0

/-- The Gamma shape `β_{r,j} = (r+1+j)/d` (`sec:gamma`). -/
noncomputable def shapeD (d r j : ℕ) : ℝ := ((r : ℝ) + 1 + j) / d

/-- The limit constant of Corollary 4.2:
`π r! d^{-(d-2)β_r} ∏_{j ∈ J_r \ {j_r}} Γ(β_{r,j} - β_r)/Γ(β_{r,j})`, with
`β_r = β_{r,j_r}`. -/
noncomputable def endpointConst (d r : ℕ) : ℝ :=
  Real.pi * r.factorial * (d : ℝ) ^ (-((d : ℝ) - 2) * shapeD d r (jMin d r)) *
    ∏ j ∈ (Finset.range d).filter (fun j => j ≠ d - 1 - r ∧ j ≠ jMin d r),
      Real.Gamma (shapeD d r j - shapeD d r (jMin d r)) / Real.Gamma (shapeD d r j)

/-- **Corollary 4.2** (`cor:endpoint`).

For `d ≥ 2` and `0 ≤ r ≤ d - 1`,
`a^{-j_r} ∫|z|^{2r}ρ_a dA → endpointConst d r ∈ (0, ∞)` as `a → 0⁺`.
Consequently, as `a → 0⁺`, the leading Gram matrices of sizes `n ≤ d - 1`
(orders `N = n - 1 ≤ d - 2`) converge to nonsingular diagonal matrices, while
the one of size `d` (order `N = d - 1`) converges to a diagonal matrix of
rank `d - 1`.

Demand sheet (paper lines 670–680 of `v2.2`):
- `d ≥ 2`, every `r < d`.
- limit: operational `Tendsto` along `𝓝[>] 0`, with the explicit constant,
  and its strict positivity.
- consequences: for every size `n < d` a limit matrix exists, is diagonal and
  has nonzero determinant; for size `d` a limit matrix exists, is diagonal
  and has rank exactly `d - 1`. -/
def Stmt_endpoint : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    (∀ r < d, 0 < endpointConst d r ∧
      Tendsto (fun a : ℝ => ((a : ℂ) ^ jMin d r)⁻¹ * momentD d a r) (𝓝[>] 0)
        (𝓝 (endpointConst d r : ℂ))) ∧
    (∀ n < d, ∃ L : Matrix (Fin n) (Fin n) ℂ,
      Tendsto (fun a : ℝ => gramLeadD d a n) (𝓝[>] 0) (𝓝 L) ∧
        (∀ i j, i ≠ j → L i j = 0) ∧ L.det ≠ 0) ∧
    ∃ L : Matrix (Fin d) (Fin d) ℂ,
      Tendsto (fun a : ℝ => gramLeadD d a d) (𝓝[>] 0) (𝓝 L) ∧
        (∀ i j, i ≠ j → L i j = 0) ∧ L.rank = d - 1

end Painleve
