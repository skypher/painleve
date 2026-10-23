You are an independent referee checking the description of a Lean 4 / Mathlib formalization in a mathematics paper. You work alone.

Release v2.3 of the repository changed three passages of paper.tex (diff below): the last paragraph of the introduction's outline, one sentence of the acknowledgments, and the "Code availability" section. The README and lean/LEDGER.md were changed to match. Decide whether these passages describe the formalization accurately, and in particular whether they overclaim.

Check:
1. Coverage. The passages say Lean verifies Theorems 1.1, 1.2 and 1.3 and Corollary 4.2. Compare each paper statement (full paper below) with the frozen Lean statements (Statement.lean, StatementUnique.lean, StatementD.lean below) that are said to formalize it: `Stmt_mainD` (Theorem 1.1), `Stmt_main` (case d = 4 of Theorem 1.1 with Theorem 1.2), `Stmt_uniqueD` (Theorem 1.3), `Stmt_endpoint` (Corollary 4.2). Is any assertion of these four results, including "in particular" clauses, well-definedness claims and "consequently" clauses, missing from or weaker in the Lean statements? If so, the claim "formally verified" overclaims for that result: say exactly which part, and give the corrected wording.
2. Routes. The code availability section says the general-d proofs follow Sections 2-6 and 8 of the paper, except that Proposition 4.1 is proved by comparing characteristic functions (Gauss's multiplication formula in law) instead of Mellin transforms, and that the proof of Theorem 1.2 and of the d = 4 case of the last assertion of Theorem 1.3 follows the quartic arguments of release v1.1. Compare these with the module docstrings below. Flag anything inaccurate or misleading.
3. Consistency. Check names, release tag, file paths, the list of what lean/Check.lean checks (its output is below), and agreement between the paper, README and LEDGER passages.
4. Wording. Note any sentence that is unclear, or that a referee would object to.

You cannot run Lean. Take as given that `lake build` succeeds and that lean/Check.lean prints the output shown (each `example : Stmt := thm` type-checks; the axioms of each theorem are among propext, Classical.choice, Quot.sound).

Report PASS/FAIL for each of items 1-4 with reasons, an overall verdict (ACCEPT, MINOR CHANGES, or REJECT), and replacement text for every change you require.

=== git diff v2.2..v2.3 -- paper.tex ===
diff --git a/paper.tex b/paper.tex
index c7c087d..7e7c26e 100644
--- a/paper.tex
+++ b/paper.tex
@@ -354,15 +354,10 @@ Section~\ref{sec:signs} proves Theorem~\ref{thm:main}(i).
 Section~\ref{sec:completion} derives the recurrence and proves
 Theorem~\ref{thm:main}(ii).  Section~\ref{sec:quartic} treats \(d=4\)
 and proves Theorem~\ref{thm:quartic}, and Section~\ref{sec:unique}
-proves Theorem~\ref{thm:unique}.  For \(d=4\), Theorems~\ref{thm:main}
-and~\ref{thm:quartic} and the uniqueness assertion of
-Theorem~\ref{thm:unique} (not its asymptotic assertion) have been
-formally verified in Lean~4.33.0 with Mathlib, as the declarations
-\path{Painleve.main_theorem} and \path{Painleve.unique_theorem}.  That
-formalization follows earlier, quartic-specific forms of the arguments
-(see the code availability statement); the general-\(d\) arguments of
-Sections~\ref{sec:hankel}--\ref{sec:completion} and~\ref{sec:unique}
-have not been formalized.
+proves Theorem~\ref{thm:unique}.  Theorems~\ref{thm:main},
+\ref{thm:quartic} and~\ref{thm:unique} and
+Corollary~\ref{cor:endpoint} have been formally verified in Lean~4.33.0
+with Mathlib (see the code availability statement).
 
 \section{The Gram form}\label{sec:gram}
 
@@ -1360,7 +1355,8 @@ and~\ref{sec:signs}) was developed with assistance from Anthropic's
 Claude Code using Claude Opus~5.5.  The manuscript was revised, and the
 Lean formalization of the case \(d=4\) was produced, with assistance
 from Claude Code using Claude Opus~5.5, Claude Fable~5 and Claude
-Haiku~5.5.  The proof of Theorem~\ref{thm:unique}, by comparison
+Haiku~5.5; the Lean formalization for general \(d\) was produced with
+assistance from Claude Code using Claude Opus~5.5.  The proof of Theorem~\ref{thm:unique}, by comparison
 with an approximate solution, and the weighted energy estimate of an
 earlier proof for \(d=4\) were obtained in consultations with OpenAI's
 GPT-6 Pro, which was also used for independent referee-style checks of
@@ -1373,22 +1369,30 @@ mathematical claims, citations, computations, and wording.
 
 \section*{Code availability}
 
-The Lean~4 formalization of the case \(d=4\) of
-Theorem~\ref{thm:main}, of Theorem~\ref{thm:quartic}, and of the
-uniqueness assertion of Theorem~\ref{thm:unique} for \(d=4\) is in the
+The Lean~4 formalization of Theorems~\ref{thm:main}, \ref{thm:quartic}
+and~\ref{thm:unique} and of Corollary~\ref{cor:endpoint} is in the
 directory \path{lean} of release
-\path{v2.1} of the repository
+\path{v2.3} of the repository
 \href{https://github.com/skypher/painleve}{github.com/skypher/painleve}
-(Lean~4.33.0, Mathlib commit \path{db584cd6d46c}).  It follows the
-quartic arguments of the version of this paper in release \path{v1.1}.
-The statements \path{Painleve.Stmt_main} (the case \(d=4\) of
-Theorem~\ref{thm:main} with Theorem~\ref{thm:quartic}) and
-\path{Painleve.Stmt_unique} (the uniqueness assertion of
-Theorem~\ref{thm:unique} for \(d=4\)) are proved by
-\path{Painleve.main_theorem} and \path{Painleve.unique_theorem}.  These
-proofs use only the axioms \path{propext}, \path{Classical.choice} and
+(Lean~4.33.0, Mathlib commit \path{db584cd6d46c}).  The statements
+\path{Painleve.Stmt_mainD} (Theorem~\ref{thm:main}),
+\path{Painleve.Stmt_main} (the case \(d=4\) of Theorem~\ref{thm:main}
+with Theorem~\ref{thm:quartic}), \path{Painleve.Stmt_uniqueD}
+(Theorem~\ref{thm:unique}) and \path{Painleve.Stmt_endpoint}
+(Corollary~\ref{cor:endpoint}) are proved by
+\path{Painleve.main_theoremD}, \path{Painleve.main_theorem},
+\path{Painleve.unique_theoremD} and \path{Painleve.endpoint_theorem}.
+The proofs for general \(d\) follow
+Sections~\ref{sec:gram}--\ref{sec:completion} and~\ref{sec:unique},
+except that Proposition~\ref{prop:gamma} is proved there by comparing
+characteristic functions (Gauss's multiplication formula in law for
+logarithms of Gamma variables) instead of Mellin transforms.  The proof
+of Theorem~\ref{thm:quartic}, and of the case \(d=4\) of the last
+assertion of Theorem~\ref{thm:unique}, follows the quartic arguments of
+the version of this paper in release \path{v1.1}.  These proofs use only
+the axioms \path{propext}, \path{Classical.choice} and
 \path{Quot.sound}; the repository README gives the build commands and
-the file \path{lean/Check.lean} that checks both.  The directory
+the file \path{lean/Check.lean} that checks them.  The directory
 \path{runs/general-d} contains numerical checks of
 Sections~\ref{sec:hankel}--\ref{sec:completion} for \(d\leq8\), and
 \path{runs/uniq} the numerical scans of initial values used as a sanity

=== README.md (lean part, v2.3) ===
- `lean/`: a Lean 4 / Mathlib formalization of Theorems 1.1, 1.2 and 1.3
  and Corollary 4.2.
  - `Painleve/StatementD.lean` holds the frozen general-`d` statements
    `Painleve.Stmt_mainD` (Theorem 1.1), `Painleve.Stmt_uniqueD`
    (Theorem 1.3) and `Painleve.Stmt_endpoint` (Corollary 4.2), proved by
    `Painleve.main_theoremD` (`Painleve/MainD.lean`),
    `Painleve.unique_theoremD` (`Painleve/UniqueD.lean`) and
    `Painleve.endpoint_theorem` (`Painleve/Endpoint.lean`). These proofs
    follow Sections 2–6 and 8 of the current paper, except that
    Proposition 4.1 is proved by comparing characteristic functions
    (Gauss's multiplication formula in law) instead of Mellin transforms.
  - `Painleve/Statement.lean` and `Painleve/StatementUnique.lean` hold the
    frozen `d = 4` statements `Painleve.Stmt_main` (Theorem 1.1 for `d = 4`
    with Theorem 1.2) and `Painleve.Stmt_unique` (uniqueness of the positive
    solution for `d = 4`), proved by `Painleve.main_theorem`
    (`Painleve/Main.lean`) and `Painleve.unique_theorem`
    (`Painleve/Unique.lean`). These follow the quartic argument of the paper
    as of release `v1.1`; section and lemma numbers in their docstrings refer
    to that version.
  - All five theorems use only the axioms `propext`, `Classical.choice` and
    `Quot.sound`.
  - `LEDGER.md` maps the paper's results to the Lean modules.
  - `Check.lean` is the acceptance check (see below).

## Building

=== lean/LEDGER.md (general-d section, v2.3) ===
## General `d` (current paper, release `v2.3`): COMPLETE, 2026-10-24

Final theorems, with statements in `Painleve/StatementD.lean` (frozen at
commit 5b3c227, byte-identical since):

- `Painleve.main_theoremD : Painleve.Stmt_mainD` (Theorem 1.1, every `d ≥ 2`);
- `Painleve.unique_theoremD : Painleve.Stmt_uniqueD` (Theorem 1.3, every
  `d ≥ 3`, with its consequences for eq:FH-recurrence and, for `d = 4`, the
  Bessel solution);
- `Painleve.endpoint_theorem : Painleve.Stmt_endpoint` (Corollary 4.2).

Statement status: APPROVED by independent statement checks (GPT-6 Pro via
pro-cli): `Stmt_mainD` and `Stmt_endpoint` job_dedb8ed6; `Stmt_uniqueD`
job_daa6c86e (after the reviewer's correction of the consequences).

Acceptance: `lake env lean Check.lean` type-checks all five theorems against
the frozen statements; each depends only on `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, `admit` or `axiom` in the 69 modules (15292 lines).

Agents: none; written in the main Claude Code session (Opus 5.5).

| Paper item (current numbering) | Lean modules |
|---|---|
| §2: Gram form, twist, weight orthogonality, block scaling | `GramD` |
| Lemma 3.1, Corollary 3.2 (two-source identity, Hankel form) | `HankelD` |
| Proposition 4.1 (Gamma representation), via Gauss multiplication in law | `GaussMult`, `GaussMultC`, `LogGamma`, `Polar`, `GammaLaw`, `GammaRep` |
| Corollary 4.2 (endpoint `a = 0`) | `EndpointProb`, `Endpoint` |
| Lemma 5.1 (Hankel signs): total positivity, Andréief, symmetrization | `ExpTP`, `PolyDeriv`, `ConvSmooth`, `SymPos`, `KernelDeriv`, `HankelSign` |
| Proposition 5.2 (block determinants), Theorem 1.1(i) | `BlockSignD`, `AssemblyD` |
| §6 (recurrence), Theorem 1.1(ii) | `HermIbpD`, `RecurrenceD`, `MainD` |
| §8: window form, crude bounds (Lemma 8.1) | `UniqD1` |
| §8: approximate solution (Lemma 8.2) and its derivatives | `UniqD2`, `UniqD3` |
| §8: energy identity and weighted bound | `UniqD4`, `UniqD5`, `UniqD6` |
| Proposition 8.3 (a priori bound) | `UniqD7` |
| Theorem 1.3: asymptotics and uniqueness; FH normalization | `UniqD8`, `UniqueD` |

## `d = 4` (paper release `v1.1`)

=== lean/Check.lean ===
import Painleve
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Acceptance check: run `lake env lean Check.lean` after `lake build`. -/

open Lean Elab Command in
/-- Enforce the dependency policy, including dependencies of dependencies. -/
elab "assert_allowed_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do
    unless allowed.contains ax do
      throwError "unexpected axiom: {ax}"
  logInfo m!"{name}: allowed axioms {axioms}"

-- Regression: a dependency through a theorem must still be rejected.
namespace AxiomAuditRegression
axiom unwanted : False
theorem indirect : False := unwanted
/-- error: unexpected axiom: AxiomAuditRegression.unwanted -/
#guard_msgs in
assert_allowed_axioms indirect
-- Exercise the built-in admitted-proof axiom without an admitted theorem.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admittedDependency : False := sorryAx False true
/-- error: unexpected axiom: sorryAx -/
#guard_msgs in
assert_allowed_axioms admittedDependency
end AxiomAuditRegression

example : Painleve.Stmt_main := Painleve.main_theorem
example : Painleve.Stmt_unique := Painleve.unique_theorem
example : Painleve.Stmt_mainD := Painleve.main_theoremD
example : Painleve.Stmt_endpoint := Painleve.endpoint_theorem
example : Painleve.Stmt_uniqueD := Painleve.unique_theoremD

assert_allowed_axioms Painleve.main_theorem
assert_allowed_axioms Painleve.unique_theorem
assert_allowed_axioms Painleve.main_theoremD
assert_allowed_axioms Painleve.endpoint_theorem
assert_allowed_axioms Painleve.unique_theoremD

=== output of lake env lean Check.lean ===
Painleve.main_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.unique_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.main_theoremD: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.endpoint_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.unique_theoremD: allowed axioms [propext, Classical.choice, Quot.sound]

=== lean/Painleve/Statement.lean ===
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

=== lean/Painleve/StatementUnique.lean ===
import Painleve.Statement

/-!
# Statement of Theorem 1.2 (uniqueness of the positive solution)

Frozen Lean statement of Theorem 1.2 of `paper.tex` (label `thm:unique`):
for every `a > 0` (so `ε = a⁻²` ranges over all positive reals), two
sequences of positive numbers satisfying the quartic recurrence
`eq:quartic-recurrence` (with `v_n = 0` for `n < 0`, encoded by `extZ`)
coincide. No initial values are prescribed.
-/

namespace Painleve

/-- **Theorem 1.2** (`thm:unique`). -/
def Stmt_unique : Prop :=
  ∀ a : ℝ, 0 < a → ∀ v w : ℕ → ℝ,
    (∀ n, 0 < v n) → (∀ n, 0 < w n) → QuarticRec a v → QuarticRec a w → v = w

end Painleve

=== lean/Painleve/StatementD.lean ===
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

=== module docstrings of the general-d modules (in dependency order) ===
--- GramD.lean
/-!
# The Gram form for general `d` (Section 2 of `paper.tex`)

The twist on monomials (`eq:twist-sign`), orthogonality of distinct weight
spaces, the block decomposition of the leading Gram determinants, and the
scaling `Δ_k^{(r)} = (-1)^{rk} d^{2·binom(k,2)} det[(i/d)^{p+q} M_{pq}^{(r)}]`
(first step of `cor:hankel`).
-/
--- HankelD.lean
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
--- GaussMult.lean
/-!
# Gauss's multiplication formula for positive real arguments

For an integer `d ≥ 1` and `s > 0`,
`Γ(s) = d^{s-1} ∏_{k<d} Γ((s+k)/d) / ∏_{k<d} Γ((1+k)/d)`
(DLMF 5.5.6, with the constant left unevaluated). The proof follows the
Bohr–Mollerup argument that Mathlib uses for the doubling formula
(`Real.doublingGamma_eq_Gamma`). The ratio form `Gamma_ratio_mult` is the
input to the Gamma representation (`prop:gamma`).
-/
--- GaussMultC.lean
/-!
# Gauss's multiplication formula on the right half-plane

The real formula `multGamma_eq_Gamma` extends to `Re s > 0` by the identity
theorem: both sides are holomorphic on the connected half-plane and agree on
the positive reals. The ratio form `cGamma_ratio_mult` gives the characteristic
functions in the Gamma representation (`prop:gamma`).
-/
--- LogGamma.lean
/-!
# Laws of logarithms of Gamma variables

If `G` has the Gamma distribution with shape `β > 0`, then `log G` has the
density `q_β(v) = e^{βv - e^v}/Γ(β)` on `ℝ` (`lem:hankel-signs`). We define
this law, the laws of sums of independent such logarithms (convolutions), and
compute their characteristic functions: `E[e^{it log G}] = Γ(β+it)/Γ(β)`.
-/
--- Polar.lean
/-!
# The weighted sources in polar coordinates

`𝒲_r(a; λ) = ∫ |z|^{2r} exp(-a|z|² + (iλ/d)(z^d + z̄^d)) dA` (Section 3 of
`paper.tex`). In polar coordinates `z = R e^{iθ}` one has
`z^d + z̄^d = 2R^d cos(dθ)`, and the angular integral of `e^{iy cos(dθ)}` over a
period equals `K(y) = ∫_{-π}^{π} e^{iy cos θ} dθ` (Step 1 of `prop:gamma`).
-/
--- GammaLaw.lean
/-!
# Gauss's multiplication formula in law

For `U ~ Gamma(r+1)` the law of `d log U` equals that of
`d log d + log G + ∑_{j ∈ J_r} log G_j`, where `G ~ Exp(1)` and the `G_j` are
independent Gamma variables with shapes `β_{r,j} = (r+1+j)/d`,
`J_r = {0,…,d-1} \ {d-1-r}`. Both laws have the same characteristic function by
the complex Gauss multiplication formula (`cGamma_ratio_mult`); the factor with
`j = d-1-r` has shape `1`. This is Steps 2–4 of `prop:gamma`.
-/
--- GammaRep.lean
/-!
# The Gamma representation (Proposition 4.1 of `paper.tex`)

`𝒲_r(a; λ) = π r! a^{-r-1} E[exp(-λ² d^{d-2} a^{-d} S_r)]`, where `S_r` is a
product of independent Gamma variables with shapes `(r+1+j)/d`,
`j ∈ J_r = {0,…,d-1} \ {d-1-r}`.

Route: polar coordinates give `𝒲_r = ∫ R^{2r+1} e^{-aR²} K((2λ/d) R^d) dR`
(`srcW_polar`); in logarithmic coordinates this is an expectation over
`log U`, `U ~ Gamma(r+1)`. Gauss's multiplication formula identifies the law
of `d log U` with that of `d log d + log G + ∑_{j ∈ J_r} log G_j`, with `G`
exponential (`law_eq`), and the Gaussian integral
`∫ e^{-|w|²} e^{2iγ Re w} dA = π e^{-γ²}` integrates out `G` (`gauss_K`).
-/
--- EndpointProb.lean
/-!
# Laplace transforms and negative moments of Gamma laws (for `cor:endpoint`)

For `G ~ Gamma(β)`: `E[e^{-cG}] = (1+c)^{-β}` (`c ≥ 0`) and
`E[G^{-s}] = Γ(β-s)/Γ(β)` (`s < β`); for a product of independent Gamma
variables the negative moments multiply.
-/
--- Endpoint.lean
/-!
# The endpoint `a = 0` (Corollary 4.2 of `paper.tex`)

`S_r = G_{r,j_r} R_r`; conditioning on `R_r` and `E[e^{-sG}] = (1+s)^{-β}` give
`a^{-j_r} ∫|z|^{2r} ρ_a = π r! d^{-(d-2)β_r} E[(κ/(1+κR_r))^{β_r}]` with
`κ = d^{d-2} a^{-d}`; as `a → 0⁺`, `κ → ∞` and dominated convergence gives the
limit `π r! d^{-(d-2)β_r} E[R_r^{-β_r}]`.
-/
--- ExpTP.lean
/-!
# Strict total positivity of the kernel `e^{ξζ}`

For `ξ_1 < ⋯ < ξ_k` and `ζ_1 < ⋯ < ζ_k`, `det[e^{ξ_i ζ_l}] > 0`
(`lem:hankel-signs`). A nonzero sum `∑_l c_l e^{ζ_l ξ}` has at most `k - 1`
real zeros, by induction on `k` with Rolle's theorem applied to
`e^{-ζ_1 ξ} ∑_l c_l e^{ζ_l ξ}`; so the determinant never vanishes on the
convex set of increasing `ζ`. Deforming `ζ` linearly to `(0, 1, …, k-1)`, where
the determinant is a Vandermonde determinant in `e^{ξ_i}`, fixes its sign.
-/
--- PolyDeriv.lean
/-!
# Derivatives of `exp(βv - c e^v)`

`d^n/dv^n exp(βv - c e^v) = exp(βv - c e^v) P_n(e^v)` with `P_0 = 1` and
`P_{n+1}(y) = (β - c y) P_n(y) + y P_n'(y)`; `P_n` has degree at most `n` and
`y^n`-coefficient `(-c)^n` (`lem:hankel-signs`). Consequently
`det[P_q(y_i)]_{i,q<k} = (-c)^{k(k-1)/2} V(y)`.
-/
--- ConvSmooth.lean
/-!
# Convolution with a log-Gamma density preserves bounded smoothness

`(T_β f)(u) = ∫ q_β(x) f(u + x) dx = E[f(u + log G)]`, `G ~ Gamma(β)`. If `f` is
smooth with bounded derivatives of every order, so is `T_β f`, and
`(T_β f)^{(n)} = T_β (f^{(n)})` (`lem:hankel-signs`: "by induction and dominated
convergence, each `φ_j` is smooth with bounded derivatives").
-/
--- SymPos.lean
/-!
# Positivity of symmetric integrals over `ℝ^k`

If `F` is integrable on `ℝ^k`, invariant under permutations of the coordinates,
and `s F(w) > 0` at every strictly increasing `w`, then `s ∫ F > 0`. Points with
two equal coordinates form a null set, and every other point is a permutation
of an increasing one (`lem:hankel-signs`: "together with the symmetry of the
integrand", "the integrand has sign `(-1)^{k(k-1)/2}` and does not vanish").
-/
--- KernelDeriv.lean
/-!
# Differentiating `∫ g(w) q_β(w - u) dw` on the kernel

For bounded continuous `g`,
`∂_u^j ∫ g(w) q_β(w-u) dw = ∫ g(w) (-1)^j q_β^{(j)}(w-u) dw`, where
`q_β^{(j)}(v) = q_β(v) P_j(e^v)` (`lem:hankel-signs`, final step: "On `|u| ≤ M`,
`|q_m^{(q)}(w-u)| ≤ C e^{β_m w}(1+e^w)^q exp(-e^{-M} e^w)`, which is integrable").
-/
--- HankelSign.lean
/-!
# Signs of the Hankel determinants (Lemma 5.1 of `paper.tex`)

For shapes `β_1, …, β_m > 0` (`m ≥ 1`) let
`φ(u) = E[exp(-e^u G_1 ⋯ G_m)] = ∫ exp(-e^{u+y}) d(prodLaw βs)(y)`. Then
`(-1)^{k(k-1)/2} det[φ^{(p+q)}(u)]_{p,q<k} > 0` for every `u` and `k`.

`φ_0(u) = exp(-e^u)` and `φ_j = T_{β_j} φ_{j-1}`, with
`(T_β f)(u) = ∫ f(w) q_β(w-u) dw`. The claim
`sgn det[φ_j^{(p)}(u_l)] = (-1)^{k(k-1)/2}` for `u_1 < ⋯ < u_k` follows by
induction from Andréief's identity, the symmetry of the integrand, and the
strict total positivity of `q_β(w-u) ∝ e^{βw} e^{-βu} exp(ξζ)`, `ξ = e^w`,
`ζ = -e^{-u}`. The Hankel determinant at a single point is handled the same
way after moving the `q`-derivatives onto the kernel, where they produce monic
polynomials in `e^{w-u}`.
-/
--- BlockSignD.lean
/-!
# Signs of the Gram blocks for general `d` (Proposition 5.2 of `paper.tex`)

`sgn Δ_k^{(r)} = (-1)^{rk + k(k-1)/2}`: by `cor:hankel`, `Δ_k^{(r)}` is
`(-1)^{rk} d^{2·binom(k,2)}` times the Hankel determinant of `F_r`, and by
`prop:gamma`, `F_r(t) = π r! a^{-r-1} φ(t + log κ)` with `φ` the function of
`lem:hankel-signs` for the shapes `β_{r,j}` and `κ = d^{d-2} a^{-d}`.
-/
--- AssemblyD.lean
/-!
# Theorem 1.1(i) for general `d`: nondegeneracy and positive signed norms

From the block signs (`blockGramD_sign`, Proposition 5.2):
`det G_{n+1}/det G_n = ϱ(n) c` with `c > 0` (`eq:norm-delta-ratio`,
`eq:rho-block`), so every leading Gram matrix is nondegenerate and `𝔥_n > 0`.
-/
--- HermIbpD.lean
/-!
# Hermitian symmetry and integration by parts for general `d` (Section 6)

`(f, g)_a = conj (g, f)_a`, and with `L = ∂_z + i z^{d-1}`,
`(L f, z^q)_a = -τ(q) a (f, z^{q+1})_a` (`eq:ibp-pairing`), from
`∂_z ρ_a = (-a z̄ + i z^{d-1}) ρ_a` and the vanishing of total derivatives.
-/
--- RecurrenceD.lean
/-!
# The recurrence from the Hermitian form for general `d` (Section 6 of `paper.tex`)

An abstract form `B` on `ℂ[X]`, linear in the first argument, Hermitian,
orthogonal across weights modulo `d`, with the integration by parts
`(L f, z^q) = -τ(q) a (f, z^{q+1})`, `L = ∂_z + i z^{d-1}` (`eq:ibp-pairing`).
Given monic orthogonal polynomials with signed norms `ϱ(n) 𝔥_n`, `𝔥_n > 0`:
`z P_n = P_{n+1} + c_n P_{n+1-d}` (`eq:polynomial-recurrences`), the coefficient
of `P_{n-1}` in `z^{d-1} P_n` is `∑_{s=0}^{d-2} c_{n+s}` (paths with one step
`-(d-1)`), and the norm ratios satisfy `eq:FH-recurrence`.
-/
--- MainD.lean
/-!
# Theorem 1.1 for every `d ≥ 2` (`thm:main`)

Part (i) is `main_partI`. Part (ii): the pairing satisfies the hypotheses of
Section 6, so `V_n = 𝔥_{n+1}/𝔥_n` solves `eq:FH-recurrence`
(`rec_real` and a telescoping product); `P_j = z^j` for `j ≤ d - 1`, so
`𝔥_j = ∫|z|^{2j} ρ_a` and `V_j` has the initial values `eq:FH-initial`; and a
real solution with these initial values is determined index by index, since
the recurrence at `m` is linear in `V_{m+d-2}` with coefficient
`a^{-2} V_m ⋯ V_{m+d-3} > 0`.
-/
--- UniqD1.lean
/-!
# Uniqueness for general `d`: setup and crude bounds (Section 8 of `paper.tex`)

With `T_m = v_m v_{m+1} ⋯ v_{m+d-2}`, `eq:general-recurrence` reads
`v_n + ∑_{m=n-d+2}^{n} T_m = (n+1) ε` (`eq:integrated`), where windows with a
negative index are absent. Lemma 8.1 (`lem:crude`): every positive solution
satisfies `ε/K (n+1)^{-(d-3)} ≤ v_n ≤ (n+1)ε` and `T_n ≤ (n+1)ε`, with
`K = 1 + (d-1)^{d-1} ε^{d-2}`.
-/
--- UniqD2.lean
/-!
# The approximate solution (Section 8 of `paper.tex`)

`q(t) > 0` is the root of `q + (d-1) q^{d-1} = ε t`; it is smooth and increasing.
With `f = log q`: `f' = ε/(q + (d-1)² q^{d-1})`, so `0 < f'(t) ≤ 1/t`, and
`f'' = -f'² (1 + (d-1)³ q^{d-2})/(1 + (d-1)² q^{d-2})`, so `|f''(t)| ≤ (d-1)/t²`.
-/
--- UniqD3.lean
/-!
# Lemma 8.2 (`lem:reference`): the approximate solution and its residual

`q_n = q(n+1)`, `Q_m = q_m ⋯ q_{m+d-2}`, `r_n = q_n + ∑_{m=n-d+2}^{n} Q_m - (n+1)ε`.
For `t ≥ 1`: `q(1) t^{1/(d-1)} ≤ q(t) ≤ (εt/(d-1))^{1/(d-1)}`, `q(1) ≥ ε/K`;
`Q_m ≤ (m+1)ε`; and `|r_n| ≤ 6 ε (d-1)^4/(n+1)` (the first-order Taylor terms
cancel). The paper records the constant `4`; any `C/(n+1)` serves the a priori
bound.
-/
--- UniqD4.lean
/-!
# The localized energy identity (Section 8 of `paper.tex`)

For sequences with `a_n δ_n + ∑_{m=n-d+2}^{n} b_m D_m = -r_n`
(`D_m = ∑_{i=m}^{m+d-2} δ_i`, `eq:linearized`) and finitely supported `h`,
multiplying by `h_n² δ_n`, regrouping by windows and using
`(∑ z_i)(∑ h_i² z_i) = (∑ h_i z_i)² + ½ ∑_{i,j} (h_i - h_j)² z_i z_j`
(`eq:square-identity`, symmetric form) gives `eq:localized`.
-/
--- UniqD5.lean
/-!
# Tools for the a priori bound (Proposition 8.3 of `paper.tex`)

`LM(x,y) ≥ x/(1 + |log(y/x)|)` (`eq:lm-lower`); Lipschitz bounds for the
truncated weights `h_n = (w_n - w_R)_+`, `w_n = (n+1)^{-p}`; tail sums over
windows of length `L = d - 1`; summability of `δ_n² (n+1)^{-(1+2p)}` when
`|δ_n|` grows logarithmically.
-/
--- UniqD6.lean
/-!
# The weighted energy bound (proof of Proposition 8.3 of `paper.tex`)

For `a_n δ_n + ∑_{m=n-d+2}^{n} b_m D_m = -r_n` with `a ≥ 0`, `0 ≤ b_m ≤ ε(m+1)`:
apply `eq:localized` with `h_n = (w_n - w_R)_+`, `w_n = (n+1)^{-p}`, bound the
source term by `∑ |r_n| w_n² |δ_n|` and the window term with the Lipschitz bound
for `h`, and let `R → ∞` (monotone in `R`).
-/
--- UniqD7.lean
/-!
# Proposition 8.3 (`prop:apriori`): the a priori bound and the asymptotics

For every positive solution `v` of `eq:general-recurrence` (`d ≥ 3`, `ε > 0`),
`δ_n = log(v_n/q_n)` is square summable; hence `v_n/q_n → 1` and
`v_n ((d-1)/(ε(n+1)))^{1/(d-1)} → 1`.
-/
--- UniqD8.lean
/-!
# Theorem 1.3: asymptotics and uniqueness of the positive solution

The asymptotics follow from `δ_n → 0` (Proposition 8.3) and
`q(t) ((d-1)/(εt))^{1/(d-1)} → 1`. For uniqueness, `η = log(v'/v)` is square
summable, and the energy identity with the cutoff `h = 1` on `[0, R]`, linear to
`0` on `[R, 2R]`, gives `A_n η_n² ≤ C/R` for `R ≥ n`.
-/
--- UniqueD.lean
/-!
# Theorem 1.3 (`thm:unique`)

For `d ≥ 3` and `ε > 0`, every positive solution of `eq:general-recurrence`
satisfies `v_n ((d-1)/(ε(n+1)))^{1/(d-1)} → 1`, and there is at most one.
With `V_n = a^{2/(d-2)} v_n` and `ε = a^{-d/(d-2)}`, `eq:FH-recurrence` becomes
`eq:general-recurrence`; so `V_n = 𝔥_{n+1}/𝔥_n` (Theorem 1.1(ii)) is the unique
positive solution of `eq:FH-recurrence`, and for `d = 4` the Bessel solution of
Theorem 1.2 is the unique positive solution of the quartic recurrence.
-/

=== lean/Painleve/UniqueD.lean (assembly of Stmt_uniqueD) ===
import Painleve.UniqD8
import Painleve.MainD
import Painleve.Main
import Painleve.Unique

/-!
# Theorem 1.3 (`thm:unique`)

For `d ≥ 3` and `ε > 0`, every positive solution of `eq:general-recurrence`
satisfies `v_n ((d-1)/(ε(n+1)))^{1/(d-1)} → 1`, and there is at most one.
With `V_n = a^{2/(d-2)} v_n` and `ε = a^{-d/(d-2)}`, `eq:FH-recurrence` becomes
`eq:general-recurrence`; so `V_n = 𝔥_{n+1}/𝔥_n` (Theorem 1.1(ii)) is the unique
positive solution of `eq:FH-recurrence`, and for `d = 4` the Bessel solution of
Theorem 1.2 is the unique positive solution of the quartic recurrence.
-/

open Finset Filter Topology

namespace Painleve

variable {d : ℕ}

lemma extZ_div (W : ℕ → ℝ) (c : ℝ) (t : ℤ) : extZ (fun n => W n / c) t = extZ W t / c := by
  unfold extZ; split_ifs <;> simp

/-- Reflecting both window indices: `∑_j ∏_k V_{n+j-k} = ∑_j ∏_i V_{n-j+i}`. -/
lemma window_reflect (W : ℕ → ℝ) (L n : ℕ) :
    ∑ j ∈ range L, ∏ k ∈ range L, extZ W ((n : ℤ) + j - k)
      = ∑ j ∈ range L, ∏ i ∈ range L, extZ W ((n : ℤ) - j + i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [← prod_range_reflect]
  refine prod_congr rfl fun k hk => ?_
  have hj' := mem_range.mp hj
  have hk' := mem_range.mp hk
  congr 1
  push_cast [Nat.cast_sub (show 1 ≤ L by omega), Nat.cast_sub (show j ≤ L - 1 by omega),
    Nat.cast_sub (show k ≤ L - 1 by omega)]
  ring

/-- The normalization `V = a^{2/(d-2)} v`, `ε = a^{-d/(d-2)}`. -/
theorem fhrec_to_genRec (hd : 3 ≤ d) {a : ℝ} (ha : 0 < a) {W : ℕ → ℝ} (hW : FHRec d a W) :
    GenRec d (a ^ (-(d : ℝ) / ((d : ℝ) - 2))) (fun n => W n / a ^ ((2 : ℝ) / ((d : ℝ) - 2))) := by
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  set c : ℝ := a ^ ((2 : ℝ) / ((d : ℝ) - 2)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos ha _
  have hcd : c ^ (d - 2) = a ^ 2 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, Nat.cast_sub (by omega)]
    rw [show (2 : ℝ) / ((d : ℝ) - 2) * ((d : ℝ) - (2 : ℕ)) = 2 by push_cast; field_simp]
    exact Real.rpow_two a
  have hεc : a ^ (-(d : ℝ) / ((d : ℝ) - 2)) * c = a⁻¹ := by
    rw [hc, ← Real.rpow_add ha, ← Real.rpow_neg_one]
    congr 1; field_simp; ring
  have hcd1 : c ^ (d - 1) = a ^ 2 * c := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ, hcd]
  intro n
  have h := hW n
  rw [window_reflect W (d - 1) n] at h
  have hprod : ∀ j ∈ range (d - 1), ∏ i ∈ range (d - 1), extZ (fun n => W n / c) ((n : ℤ) - j + i)
      = (∏ i ∈ range (d - 1), extZ W ((n : ℤ) - j + i)) / c ^ (d - 1) := by
    intro j _
    simp_rw [extZ_div]
    rw [prod_div_distrib, prod_const, card_range]
  rw [sum_congr rfl hprod, ← sum_div, hcd1]
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hε : a ^ (-(d : ℝ) / ((d : ℝ) - 2)) = a⁻¹ / c := by
    rw [← hεc]; field_simp
  rw [hε]
  field_simp
  field_simp at h
  linarith

/-- **Theorem 1.3** (`thm:unique`). -/
theorem unique_theoremD : Stmt_uniqueD := by
  refine ⟨fun d hd ε hε => ⟨fun v hv hrec => asymptoticsD hd hε hv hrec,
    fun v w hv hw hrv hrw => uniquenessD hd hε hv hw hrv hrw⟩, ?_, ?_⟩
  · intro d hd a ha
    obtain ⟨-, ⟨V0, hV0, -⟩, hsol⟩ := (main_theoremD d (by omega) a ha).2 hd
    -- the norm ratios are the solution of Theorem 1.1(ii)
    have hV0eq : V0 = fun n => signedNormD d a (n + 1) / signedNormD d a n :=
      funext fun n => (hsol V0 hV0 n).2
    have hpos : ∀ n, 0 < signedNormD d a (n + 1) / signedNormD d a n := fun n => by
      have := (hsol V0 hV0 n).1; rwa [hV0eq] at this
    have hrec : FHRec d a (fun n => signedNormD d a (n + 1) / signedNormD d a n) := by
      rw [← hV0eq]; exact hV0.2
    refine ⟨hpos, hrec, fun W hW hWrec => ?_⟩
    have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
    set c : ℝ := a ^ ((2 : ℝ) / ((d : ℝ) - 2)) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos ha _
    have huniq := uniquenessD hd (Real.rpow_pos_of_pos ha _)
      (v := fun n => W n / c) (w := fun n => signedNormD d a (n + 1) / signedNormD d a n / c)
      (fun n => div_pos (hW n) hc0) (fun n => div_pos (hpos n) hc0)
      (fhrec_to_genRec hd ha hWrec) (fhrec_to_genRec hd ha hrec)
    funext n
    exact (div_left_inj' hc0.ne').mp (congrFun huniq n)
  · intro a ha
    obtain ⟨-, -, -, ⟨v, hv, -⟩, hsol⟩ := main_theorem a ha
    have hvpos : ∀ n, 0 < v n := fun n => (hsol v hv n).1
    exact ⟨v, hv, hvpos, fun w hw hwrec => unique_theorem a ha w v hw hvpos hwrec hv.2.2⟩

end Painleve

=== paper.tex (v2.3, full) ===
\documentclass[twoside,10pt]{article}

\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath,amsthm,amssymb,amsfonts}
\usepackage{mathtools}
\usepackage[
  letterpaper,
  total={5.5in,8in},
  vmarginratio=1:1,
  hmarginratio=1:1,
  headsep=21pt
]{geometry}
\usepackage{xcolor}
\usepackage[
  breaklinks=false,
  linktocpage=true
]{hyperref}
% Referee copy: uncomment the next line for line numbers.
% \usepackage{lineno}\linenumbers
\hypersetup{
  colorlinks=true,
  linkcolor={purple},
  urlcolor={purple},
  citecolor={blue!80!black},
  pdfauthor={Leslie P. Polzer},
  pdftitle={Positive Solutions of the Felder-Hoppe Recurrences for Quantum Minimal Surfaces},
  pdfsubject={Felder-Hoppe Gram nondegeneracy and discrete Painleve-type recurrences},
  pdfkeywords={discrete Painleve-type recurrence, indefinite orthogonal polynomials, total positivity, Gamma distribution, quantum minimal surface}
}

\medmuskip=4mu
\thickmuskip=8mu
\setlength{\emergencystretch}{2em}

\numberwithin{equation}{section}

\newtheoremstyle{slbody}
  {8pt}
  {8pt}
  {\normalfont\slshape}
  {}
  {\bfseries}
  {.}
  {0.5em}
  {\thmname{#1}\thmnumber{ #2}%
   \thmnote{ {\normalfont\itshape(\ignorespaces#3\unskip)}}}
\theoremstyle{slbody}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}

\renewcommand{\qedsymbol}{$\blacksquare$}

\newcommand{\C}{\mathbb C}
\newcommand{\N}{\mathbb N}
\newcommand{\dd}{\,\mathrm d}
\newcommand{\ii}{\mathrm i}
\newcommand{\sgn}{\operatorname{sgn}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\e}{\mathrm e}
\newcommand{\fh}{\mathfrak h}
\newcommand{\fall}[1]{^{\underline{#1}}}
\newcommand{\stir}[2]{\genfrac\{\}{0pt}{}{#1}{#2}}
\newcommand{\E}{\mathbb E}


\title{Positive solutions of the Felder--Hoppe recurrences\\
for quantum minimal surfaces}
\author{Leslie P. Polzer}
\newcommand{\authoraffiliation}{Independent Researcher}
\newcommand{\authoremail}{polzer@fastmail.com}
\date{October 23, 2026}

\makeatletter
\renewcommand{\section}{%
  \@startsection{section}{1}{\z@}%
    {-3.5ex \@plus -1ex \@minus -.2ex}%
    {2.3ex \@plus .2ex}%
    {\normalfont\large\bfseries}}
\renewcommand{\@seccntformat}[1]{%
  \csname the#1\endcsname.\enspace}

\def\tagform@#1{%
  \maketag@@@{(\ignorespaces{\oldstylenums{#1}}\unskip\@@italiccorr)}}
\renewcommand{\eqref}[1]{%
  \textup{{\normalfont(\oldstylenums{\ref{#1}}}\normalfont)}}

\newcommand{\shorttitle}{POSITIVITY FOR THE FELDER--HOPPE RECURRENCES}
\newcommand{\shortauthors}{LESLIE P. POLZER}
\newcommand{\ps@bookheader}{%
  \renewcommand\@oddfoot{\hfil}%
  \renewcommand\@evenfoot{\hfil}%
  \renewcommand\@oddhead{%
    \ifnum\value{page}>1
      {\small\hfil\shortauthors}\hfil\thepage
    \else
      \hfil
    \fi}%
  \renewcommand\@evenhead{%
    \thepage\hfil\small\shorttitle\hfil}}
\pagestyle{bookheader}

\renewcommand{\maketitle}{%
  \begin{center}
    {\large\bfseries\@title}\\
    \vskip36pt
    \ifx\@author\@empty
      \mbox{}\par
    \else
      {\scshape\@author}\par
      \medskip
      {\small\authoraffiliation}\par
      \smallskip
      {\small\texttt{\authoremail}}\par
      \smallskip
      {\small\@date}\par
    \fi
    \vskip36pt
  \end{center}}
\makeatother

\renewenvironment{abstract}
  {\quotation\noindent\small{\bfseries\abstractname.\enspace}}
  {\endquotation}

\begin{document}
\maketitle

\begin{abstract}
For every integer \(d\geq2\) and every \(a>0\), we prove the conjecture
of Felder and Hoppe that the leading Gram matrices of their indefinite
Hermitian form with density
\(\exp\bigl(-a|z|^2+\frac{\ii}{d}(z^d+\bar z^d)\bigr)\) are
nondegenerate, and we show that all signed norms of the corresponding
orthogonal polynomials are positive.  Consequently, the discrete
Painlev\'e-type recurrence satisfied by the norm ratios, which arises
from the quantum minimal surface \(w_2=w_1^{d-1}\), has a positive
solution with the moment initial data of Felder and Hoppe.  The proof
writes the planar integral that generates each symmetry block as the
Laplace transform of a product of \(d-1\) independent Gamma variables.
The Gram blocks become Hankel matrices of these Laplace transforms, and
total positivity of the logarithmic Gamma kernels, together with
Andr\'eief's identity, fixes the sign of every leading minor.  For
\(d=4\) we identify the initial data with Bessel functions of orders
\(\pm\frac14\).  We also show that nondegeneracy does not extend
continuously to \(a=0\): the leading Gram matrix of order \(d\)
converges, as \(a\to0^+\), to a matrix of rank \(d-1\).  Finally, for every \(d\geq3\) we show that the positive
solution is unique and determine its growth, by comparing an arbitrary
positive solution with an explicit approximate solution through the
convex variational structure of the recurrence.

\vskip5pt
\noindent\textbf{Keywords.}\enspace discrete Painlev\'e-type
recurrence; indefinite orthogonal polynomials; total positivity; Gamma
distribution; quantum minimal surface.

\vskip5pt
\noindent\textbf{MSC2020 Classification.}\enspace
34M55; 39A36; 33C45; 15B48; 53A10.
\end{abstract}

\vskip50pt
\baselineskip=13.5pt
\section{Introduction}

Discrete Painlev\'e-type recurrences occur both in matrix
regularizations of minimal surfaces and as recurrences for the
coefficients of orthogonal polynomials.  For the quantum minimal
surfaces associated with the holomorphic curves \(w_2=w_1^{d-1}\),
recurrences of this type were obtained in
\cite{CornalbaTaylor1998,ArnlindHoppeKontsevich2019,Hoppe2025} (see
\cite[Section~3.1]{FelderHoppe2025}).  The quartic recurrence is written
explicitly in \cite[equation~(38)]{Hoppe2025} and
\cite[Section~5]{ClarksonEtAl2025}; those works also treat the positive
special-function solution in the cubic case \(d=3\).

Felder and Hoppe \cite{FelderHoppe2025} constructed an indefinite
Hermitian form for each \(d\) (recalled in Section~\ref{sec:gram}) and
showed that, whenever its leading Gram matrices are nondegenerate, the
ratios \(V_n\) of its orthogonal-polynomial norms obey
\begin{equation}
V_n+\frac1{a^2}\sum_{j=0}^{d-2}
\prod_{k=0}^{d-2}V_{n+j-k}=\frac{n+1}{a},
\qquad n\geq0,
\label{eq:FH-recurrence}
\end{equation}
where \(V_n=0\) for \(n<0\), with the initial values
\begin{equation}
V_j=\frac{\int_\C|z|^{2j+2}\rho_a\dd A}{\int_\C|z|^{2j}\rho_a\dd A},
\qquad 0\leq j\leq d-3,
\label{eq:FH-initial}
\end{equation}
where \(\rho_a\) is the density \eqref{eq:density}
\cite[equation~(3.3) and the display after it]{FelderHoppe2025}.  They
proved the required Gram nondegeneracy for \(d=1,2,3\) and conjectured
it for every \(d\) \cite[Conjecture~3.6 and Theorem~3.7]{FelderHoppe2025}.
The conjecture is stated for \(a\geq0\), whereas the density is
introduced for \(a>0\) \cite[Section~3.1]{FelderHoppe2025}, and the
proof of \cite[Theorem~3.7]{FelderHoppe2025} addresses \(a>0\).  At
\(a=0\) the planar moments do not converge absolutely, so a Gram matrix
at \(a=0\) requires a prescription.  One natural prescription is the
entrywise limit as \(a\to0^+\).  Under it, nondegeneracy fails at the
endpoint: by Corollary~\ref{cor:endpoint}, for every \(d\geq2\) the
leading Gram matrix of order \(d\) converges to a diagonal matrix of
rank \(d-1\), and the ratio \(V_{d-2}\) in \eqref{eq:FH-recurrence}
tends to \(0\).  The vanishing of the last diagonal entry is consistent
with the differential equation of \cite[equation~(3.5)]{FelderHoppe2025}
for \(h(a)=\int_\C\rho_a\dd A\): differentiating under the integral,
\(\int_\C|z|^{2d-2}\rho_a\dd A=(-1)^{d-1}h^{(d-1)}(a)=ah(a)+a^2h'(a)\).
For \(d=1\), the Gram matrix of order one is
\(h(a)=(\pi/a)\e^{-1/a}\) \cite[Section~4]{FelderHoppe2025}, which also
tends to \(0\).  This endpoint distinction does not affect the cases
\(a>0\) proved by Felder and Hoppe, and we prove the conjecture for
every \(a>0\).

\begin{theorem}\label{thm:main}
Let \(d\geq2\) and \(a>0\).
\begin{enumerate}
\item[\textup{(i)}] Every leading Gram matrix of the Felder--Hoppe
Hermitian form \textup{(Section~\ref{sec:gram})} is nondegenerate, and
all its signed norms \(\fh_n\) are positive.  Thus
\cite[Conjecture~3.6]{FelderHoppe2025} holds for every \(d\) and every
\(a>0\).
\item[\textup{(ii)}] Let \(d\geq3\).  The ratios
\(V_n=\fh_{n+1}/\fh_n\) form the unique real sequence that satisfies
\eqref{eq:FH-recurrence} for every \(n\geq0\) and has the initial values
\eqref{eq:FH-initial}.  In particular, this solution is positive.
\end{enumerate}
\end{theorem}

The moments in \eqref{eq:FH-initial} are explicit expectations of
Gamma variables (Proposition~\ref{prop:gamma}).  For \(d=4\), after
setting \(v_n=V_n/a\) and \(\epsilon=a^{-2}\), the recurrence
\eqref{eq:FH-recurrence} becomes
\begin{equation}
v_n\left(
1+v_{n-1}v_{n-2}
+v_{n+1}v_{n-1}
+v_{n+2}v_{n+1}
\right)
=(n+1)\epsilon ,
\qquad n\geq0,
\label{eq:quartic-recurrence}
\end{equation}
where \(v_n=0\) for \(n<0\).  The two initial values are
\begin{equation}
v_0=-\frac1a\frac{h'(a)}{h(a)},
\qquad
v_1=-\frac1a\frac{h''(a)}{h'(a)},
\label{eq:initial-values}
\end{equation}
with
\begin{equation}
\begin{split}
h(a)=\frac{\pi^2a}{4}\bigg[
&J_{-1/4}\left(\frac{a^2}{4}\right)^2
-\sqrt2\,J_{-1/4}\left(\frac{a^2}{4}\right)
J_{1/4}\left(\frac{a^2}{4}\right)\\
&+J_{1/4}\left(\frac{a^2}{4}\right)^2
\bigg].
\end{split}
\label{eq:h-bessel}
\end{equation}
This is the function \(h(a)=\int_\C\rho_a\dd A\) of
\cite[equation~(3.4)]{FelderHoppe2025} for \(d=4\), in the Bessel form
given in \cite[Section~4]{FelderHoppe2025}; Lemma~\ref{lem:bessel}
below rederives it.

\begin{theorem}\label{thm:quartic}
Let \(a>0\).  The initial values
\eqref{eq:initial-values}--\eqref{eq:h-bessel} are well defined and
extend uniquely to a real sequence satisfying
\eqref{eq:quartic-recurrence} for every \(n\geq0\).  This sequence is
\(v_n=\fh_{n+1}/(a\fh_n)\) for \(d=4\); in particular, \(v_n(a)>0\) for
every \(n\geq0\).
\end{theorem}

Uniqueness in Theorems~\ref{thm:main}(ii) and~\ref{thm:quartic} refers
to the prescribed initial data.  For \(d\geq3\), the substitution
\(V_n=a^{2/(d-2)}v_n\) and \(\epsilon=a^{-d/(d-2)}\) turns
\eqref{eq:FH-recurrence} into
\begin{equation}
v_n+\sum_{m=n-d+2}^{n}v_mv_{m+1}\cdots v_{m+d-2}=(n+1)\epsilon,
\qquad n\geq0,
\label{eq:general-recurrence}
\end{equation}
where \(v_n=0\) for \(n<0\); for \(d=4\) this is
\eqref{eq:quartic-recurrence}.  The next theorem shows that the positive
solution itself is unique, so that the moment values
\eqref{eq:FH-initial}, and for \(d=4\) the Bessel values
\eqref{eq:initial-values}, are the only initial values leading to a
positive solution.

\begin{theorem}\label{thm:unique}
Let \(d\geq3\) and \(\epsilon>0\).  Every sequence of positive numbers
\((v_n)_{n\geq0}\) satisfying \eqref{eq:general-recurrence} for every
\(n\geq0\) satisfies
\[
\lim_{n\to\infty}v_n\left(\frac{d-1}{\epsilon(n+1)}\right)^{1/(d-1)}=1,
\]
and there is at most one such sequence.  In particular, for \(a>0\) the
sequence \((V_n)\) of Theorem~\ref{thm:main}(ii) is the unique positive
solution of \eqref{eq:FH-recurrence}, and for \(d=4\) the sequence of
Theorem~\ref{thm:quartic} is the unique positive solution of
\eqref{eq:quartic-recurrence}.
\end{theorem}

For the cubic analogue, the existence of a positive solution was
proved in \cite[Section~7]{ArnlindHoppeKontsevich2019} and its
uniqueness in \cite[Theorem~2.1, proved in Section~4.2]{ClarksonEtAl2025};
for \(d=3\), Theorem~\ref{thm:unique} gives a short proof of that
uniqueness.  For the quartic recurrence, \cite[Section~5]{ClarksonEtAl2025}
reports preliminary evidence for a positive solution with analogous
properties.  Our proof of Theorem~\ref{thm:unique}
(Section~\ref{sec:unique}) uses only the recurrence and is independent of
the rest of the paper.  In logarithmic variables the recurrence is the
stationarity condition of a convex functional.  Comparing an arbitrary
positive solution with an explicit approximate solution, whose residual
is \(O(n^{-1})\), gives an a priori bound in which the convexity is
controlled by the known approximate solution rather than by the unknown
one, and a cutoff argument then compares two positive solutions.

The proof of Theorem~\ref{thm:main}(i) treats all \(d\) and all indices
at once.  Independent source parameters \(u\) and \(v\) for \(z^d\) and
\(\bar z^d\) are used on disks, where the two-source integral is entire
and, by rotation invariance, depends only on \(uv\).  In exponential
coordinates \(u=\e^{t_1}\), \(v=\e^{t_2}\) this turns the Gram block of
each residue class modulo \(d\), after a unitriangular Stirling
transformation, into the Hankel matrix of derivatives of a single
kernel \(F_r(t)\), the planar integral with weight \(|z|^{2r}\) and
coupling \(\e^{t/2}\) (Lemma~\ref{lem:source-moments}).  A Mellin
transform and Gauss's multiplication formula show that \(F_r\) is the
Laplace transform, in \(\e^t\), of a product of \(d-1\) independent
Gamma variables (Proposition~\ref{prop:gamma}).  The signs of its Hankel
determinants then follow from total positivity: the densities of
logarithms of Gamma variables are totally positive convolution kernels,
and Andr\'eief's identity writes each Hankel determinant as an integral
of a product of two determinants of fixed sign
(Lemma~\ref{lem:hankel-signs}).  This determinant step is a continuous
Cauchy--Binet argument of the kind used for biorthogonal ensembles
\cite{Borodin1998}.  To our knowledge, the new ingredients are the
two-source representation, which separates the insertions of \(z^d\)
and \(\bar z^d\) that a common coupling mixes, and the Gamma-product
form of the kernels.

Section~\ref{sec:gram} recalls the Hermitian form.
Section~\ref{sec:hankel} reduces the Gram blocks to Hankel determinants,
Section~\ref{sec:gamma} proves the Gamma representation, and
Section~\ref{sec:signs} proves Theorem~\ref{thm:main}(i).
Section~\ref{sec:completion} derives the recurrence and proves
Theorem~\ref{thm:main}(ii).  Section~\ref{sec:quartic} treats \(d=4\)
and proves Theorem~\ref{thm:quartic}, and Section~\ref{sec:unique}
proves Theorem~\ref{thm:unique}.  Theorems~\ref{thm:main},
\ref{thm:quartic} and~\ref{thm:unique} and
Corollary~\ref{cor:endpoint} have been formally verified in Lean~4.33.0
with Mathlib (see the code availability statement).

\section{The Gram form}\label{sec:gram}

Fix \(d\geq2\) and \(a>0\), and put
\begin{equation}
\rho_a(z)=
\exp\left(-a|z|^2+\frac{\ii}{d}(z^d+\bar z^d)\right),
\label{eq:density}
\end{equation}
the density of \cite[Section~3.1]{FelderHoppe2025}.  The Gaussian
factor makes all polynomial moments absolutely convergent.  Let
\(\eta=\e^{\pi\ii/d}\).  Since \(\eta^d=-1\),
\[
\rho_a(\zeta z)=\rho_a(z)\quad(\zeta^d=1),
\qquad
\rho_a(\eta z)=\overline{\rho_a(z)}.
\]
Decompose the polynomial ring into weight spaces
\[
\C[z]=\bigoplus_{r=0}^{d-1}\mathcal P_r,
\qquad
\mathcal P_r=\{f\in\C[z]:f(\zeta z)=\zeta^r f(z)\text{ for }\zeta^d=1\}
=\Span\{z^{r+dq}:q\geq0\}.
\]
For \(f\in\mathcal P_r\), set \((\sigma f)(z)=(-\eta)^{-r}f(\eta z)\),
extend \(\sigma\) linearly to \(\C[z]\), and define
\begin{equation}
(f,g)_a
=\int_{\C}f(z)\overline{\sigma g(z)}\rho_a(z)\dd A(z),
\qquad
\dd A=\dd(\operatorname{Re}z)\dd(\operatorname{Im}z),
\label{eq:pairing}
\end{equation}
which is linear in \(f\) and conjugate-linear in \(g\).  This is the
Hermitian form of \cite[Proposition~3.1]{FelderHoppe2025}, with the
right inverse \(\chi(r)=r\) \((0\leq r\leq d-1)\) chosen there.  If
\(m=r+dq\) with \(0\leq r\leq d-1\), then
\begin{equation}
\sigma z^m=(-\eta)^{-r}\eta^m z^m=(-1)^{r+q}z^m.
\label{eq:twist-sign}
\end{equation}
Since \(\sigma\) preserves each \(\mathcal P_r\) and \(\rho_a\) is
invariant under \(z\mapsto\zeta z\), distinct weight spaces are
orthogonal.  On \(\mathcal P_r\), in the basis \(z^r,z^{r+d},\ldots\),
the Gram matrix is therefore
\begin{equation}
G_{pq}^{(r)}
=(z^{r+dp},z^{r+dq})_a=(-1)^{r+q}M_{pq}^{(r)},
\qquad
M_{pq}^{(r)}=\int_{\C}
z^{r+dp}\bar z^{r+dq}\rho_a(z)\dd A(z).
\label{eq:gram-block}
\end{equation}
The substitution \(z\mapsto\eta z\) and
\(\rho_a(\eta z)=\overline{\rho_a(z)}\) give
\(\overline{M_{qp}^{(r)}}=(-1)^{q-p}M_{pq}^{(r)}\), so each \(G^{(r)}\) is
a Hermitian matrix.

For \(k\geq1\), let
\begin{equation}
\Delta_k^{(r)}
=\det[G_{pq}^{(r)}]_{p,q=0}^{k-1},
\qquad
\Delta_0^{(r)}=1.
\label{eq:Delta}
\end{equation}
Assume for the moment that all \(\Delta_k^{(r)}\) are nonzero.  After
the monomials \(1,z,\ldots,z^N\) are grouped by residue modulo \(d\),
their Gram matrix is block diagonal, with leading principal submatrices
of the \(G^{(r)}\) as blocks.  Hence every leading Gram matrix
\(\big[(z^p,z^q)_a\big]_{p,q=0}^{N}\) is nondegenerate, and Gram--Schmidt
gives unique monic orthogonal polynomials \(P_n(z)=z^n+\cdots\).
Orthogonalizing \(z^n\) against lower monomials subtracts only
components in the weight space of \(z^n\), so
\(P_n\in\mathcal P_{n\bmod d}\).  Following
\cite[Lemma~3.4 and Example~3.5]{FelderHoppe2025}, for \(\ell\in\mathbb Z\)
put
\begin{equation}
\tau(\ell)=
\begin{cases}
(-1)^{d-1},&\ell\equiv-1\pmod d,\\
1,&\text{otherwise},
\end{cases}
\qquad
\varrho(n)=(-1)^n\prod_{\ell=0}^{n-1}\tau(\ell).
\label{eq:rho-sign}
\end{equation}
If \(n=r+dj\) with \(0\leq r\leq d-1\), exactly \(j\) of the integers
\(0,\ldots,n-1\) are congruent to \(d-1\), so
\begin{equation}
\varrho(r+dj)=(-1)^{r+dj+(d-1)j}=(-1)^{r+j}.
\label{eq:rho-block}
\end{equation}
The signed norms \(\fh_n\) of \cite[Section~3.1]{FelderHoppe2025},
denoted \(h_n\) there, are defined by
\begin{equation}
(P_n,P_n)_a=\varrho(n)\fh_n.
\label{eq:signed-norm}
\end{equation}
The matrices \(\big[(z^p,z^q)_a\big]_{p,q=0}^{N}\) are exactly the Gram
matrices of \cite[Conjecture~3.6]{FelderHoppe2025}.

\section{Gram blocks as Hankel determinants}\label{sec:hankel}

We write \(\binom k2=k(k-1)/2\) and \(\stir{q}{j}\) for the Stirling numbers
of the second kind, defined by \(\stir00=1\), \(\stir q j=0\) for \(j>q\)
or \(j=0<q\), and \(\stir{q+1}{j}=j\stir qj+\stir q{j-1}\).  For a
function \(G\) that is smooth on \((0,\infty)\), induction on \(q\) gives
\begin{equation}
\frac{\dd^q}{\dd t^q}G(\e^t)
=\sum_{j=0}^q\stir qj\e^{jt}G^{(j)}(\e^t),
\label{eq:stirling}
\end{equation}
because \(\frac{\dd}{\dd t}\bigl[\e^{jt}G^{(j)}(\e^t)\bigr]
=j\e^{jt}G^{(j)}(\e^t)+\e^{(j+1)t}G^{(j+1)}(\e^t)\).

For \(r\in\{0,\ldots,d-1\}\) and \(\lambda\geq0\), define the weighted
sources
\[
\mathcal W_r(a;\lambda)
=\int_{\C}|z|^{2r}
\exp\left(-a|z|^2+\frac{\ii\lambda}{d}(z^d+\bar z^d)\right)
\dd A(z),
\qquad
F_r(t)=\mathcal W_r(a;\e^{t/2}).
\]

\begin{lemma}[two-source identity]
\label{lem:source-moments}
For \(r\in\{0,\ldots,d-1\}\) and all \(p,q\geq0\),
\begin{equation}
\sum_{k=0}^p\sum_{l=0}^q\stir pk\stir ql
\left(\frac{\ii}{d}\right)^{k+l}M_{kl}^{(r)}
=F_r^{(p+q)}(0).
\label{eq:source-moments}
\end{equation}
\end{lemma}

\begin{proof}
For \(R>0\) and \(u,v\in\C\), define the disk integral
\[
\mathcal Z_R(u,v)
=\int_{|z|\leq R}|z|^{2r}
\exp\left(-a|z|^2+\frac{\ii}{d}(uz^d+v\bar z^d)\right)\dd A(z).
\]
Over the compact disk, all derivatives in \((u,v)\) may be taken under
the integral sign, and \(\mathcal Z_R\) is entire in each variable.

\emph{Step 1: \(\mathcal Z_R(u,v)=\mathcal Z_R(uv,1)\) for \(u,v>0\).}
For fixed \(u,v>0\), the function
\(H(s)=\mathcal Z_R(u\e^s,v\e^{-s})\) is entire in \(s\in\C\).  The
rotation \(z\mapsto\e^{\ii\varphi/d}z\), \(\varphi\in\mathbb R\),
preserves the disk, \(|z|\) and the area measure, and multiplies \(z^d\)
by \(\e^{\ii\varphi}\) and \(\bar z^d\) by \(\e^{-\ii\varphi}\); hence
\(H(s+\ii\varphi)=H(s)\).  Differentiating in \(\varphi\) at
\(\varphi=0\) gives \(\ii H'(s)=0\), so \(H\) is constant, and
\(H(0)=H(\log v)\) is the claim.

\emph{Step 2: the truncated identity.}  For real \(t_1,t_2\) put
\(K(t_1,t_2)=\mathcal Z_R(\e^{t_1},\e^{t_2})\).  By Step~1,
\(K(t_1,t_2)=f_R(t_1+t_2)\) with \(f_R(t)=\mathcal Z_R(\e^{t/2},\e^{t/2})\),
so \(\partial_{t_2}^q\partial_{t_1}^pK(0,0)=f_R^{(p+q)}(0)\).  On the other
hand, \eqref{eq:stirling} with \(G(w)=\exp(cw)\) gives
\(\frac{\dd^p}{\dd t^p}\exp(c\e^t)=\sum_k\stir pk(c\e^t)^k\exp(c\e^t)\);
applying this under the integral, first with \(c=\ii z^d/d\) and then
with \(c=\ii\bar z^d/d\), yields
\[
\partial_{t_2}^q\partial_{t_1}^pK(0,0)
=\sum_{k=0}^p\sum_{l=0}^q\stir pk\stir ql
\left(\frac{\ii}{d}\right)^{k+l}
\int_{|z|\leq R}z^{r+dk}\bar z^{r+dl}\rho_a(z)\dd A(z),
\]
where \(|z|^{2r}z^{dk}\bar z^{dl}=z^{r+dk}\bar z^{r+dl}\).

\emph{Step 3: \(R\to\infty\).}  The truncated moments converge to
\(M_{kl}^{(r)}\), since their integrands are bounded by
\(|z|^{2r+dk+dl}\e^{-a|z|^2}\).  For real \(t\), the factor
\(\exp\bigl(\frac{\ii}{d}\e^{t/2}(z^d+\bar z^d)\bigr)\) has modulus \(1\),
and by \eqref{eq:stirling} its \(t\)-derivatives of order \(m\) are this
factor times a polynomial in \(\e^{t/2}(z^d+\bar z^d)\); for \(|t|\leq1\)
they are bounded by \(c_m(1+|z|)^{dm}\).  Hence derivatives of all
orders may be taken under the integral both for \(f_R\) and for
\(F_r\), and dominated convergence gives
\(f_R^{(m)}(0)\to F_r^{(m)}(0)\).  Letting \(R\to\infty\) in Step~2
proves \eqref{eq:source-moments}.
\end{proof}

\begin{corollary}\label{cor:hankel}
For \(r\in\{0,\ldots,d-1\}\) and \(k\geq1\),
\begin{equation}
\Delta_k^{(r)}=(-1)^{rk}d^{2\binom k2}\det\left[F_r^{(p+q)}(0)\right]_{p,q=0}^{k-1}.
\label{eq:Delta-hankel}
\end{equation}
\end{corollary}

\begin{proof}
By \eqref{eq:gram-block},
\(G_{pq}^{(r)}=(-1)^{r+q}(d/\ii)^{p+q}\bigl[(\ii/d)^{p+q}M_{pq}^{(r)}\bigr]\).
Taking \((d/\ii)^p\) out of row \(p\) and \((-1)^{r+q}(d/\ii)^q\) out of
column \(q\), and using \((d/\ii)^2=-d^2\), gives
\(\Delta_k^{(r)}=(-1)^{rk}d^{2\binom k2}\det[(\ii/d)^{p+q}M_{pq}^{(r)}]_{p,q<k}\).
The left-hand side of \eqref{eq:source-moments} is the \((p,q)\) entry
of \(\Sigma\,[(\ii/d)^{k+l}M_{kl}^{(r)}]\,\Sigma^{\mathsf T}\), where
\(\Sigma_{pk}=\stir pk\) is lower triangular with ones on the diagonal;
its \(k\times k\) truncations therefore have the same determinant.
\end{proof}

\section{The kernels as Laplace transforms}\label{sec:gamma}

A random variable \(G\) has the Gamma distribution with shape
\(\beta>0\) if it has density \(x^{\beta-1}\e^{-x}/\Gamma(\beta)\) on
\((0,\infty)\); then \(\E[G^{-z}]=\Gamma(\beta-z)/\Gamma(\beta)\) for
\(\operatorname{Re}z<\beta\).  For \(r\in\{0,\ldots,d-1\}\) let
\[
J_r=\{0,1,\ldots,d-1\}\setminus\{d-1-r\},
\qquad
\beta_{r,j}=\frac{r+1+j}{d}\quad(j\in J_r),
\]
let \(G_{r,j}\), \(j\in J_r\), be independent Gamma variables with
shapes \(\beta_{r,j}\), and put \(S_r=\prod_{j\in J_r}G_{r,j}\), a product
of \(d-1\) factors.

\begin{proposition}[Gamma representation]\label{prop:gamma}
For \(r\in\{0,\ldots,d-1\}\) and \(\lambda\geq0\),
\begin{equation}
\mathcal W_r(a;\lambda)
=\pi\,r!\,a^{-r-1}\,
\E\left[\exp\bigl(-\lambda^2d^{\,d-2}a^{-d}S_r\bigr)\right].
\label{eq:gamma-rep}
\end{equation}
In particular, \(\int_\C|z|^{2r}\rho_a\dd A=\pi r!\,a^{-r-1}
\E[\exp(-d^{\,d-2}a^{-d}S_r)]\), and
\(F_r(t)=\pi r!\,a^{-r-1}\E[\exp(-\e^t\kappa S_r)]\) with
\(\kappa=d^{\,d-2}a^{-d}\).
\end{proposition}

\begin{proof}
At \(\lambda=0\) both sides equal \(\pi r!\,a^{-r-1}\).  The substitution
\(z\mapsto a^{-1/2}z\) gives
\(\mathcal W_r(a;\lambda)=a^{-r-1}\mathcal W_r(1;\lambda a^{-d/2})\), so
we may take \(a=1\) and \(\lambda>0\).

\emph{Step 1: a radial integral.}  In polar coordinates
\(z=R\e^{\ii\theta}\), \(z^d+\bar z^d=2R^d\cos(d\theta)\), and
\(\int_0^{2\pi}\e^{\ii x\cos(d\theta)}\dd\theta=2\pi J_0(x)\)
\cite[equation~(10.9.2)]{NISTHandbook2010}.  With \(u=R^2\),
\[
\mathcal W_r(1;\lambda)
=\pi\int_0^\infty u^r\e^{-u}J_0\bigl(c\lambda u^{d/2}\bigr)\dd u,
\qquad c=\frac2d.
\]

\emph{Step 2: the Mellin transform.}  Write
\(g(x)=\mathcal W_r(1;\sqrt x)\) for \(x>0\), and let
\(0<\operatorname{Re}z=\sigma<\min(\frac14,\frac{r+1}d)\).  Since
\(|J_0(y)|\leq1\) and \(|J_0(y)|\leq Cy^{-1/2}\)
\cite[equations~(10.14.1) and (10.17.3)]{NISTHandbook2010},
\(\int_0^\infty y^{2\sigma-1}|J_0(y)|\dd y<\infty\).  The substitution
\(y=c\sqrt x\,u^{d/2}\) gives
\(\int_0^\infty x^{\sigma-1}|J_0(c\sqrt x\,u^{d/2})|\dd x
=2(cu^{d/2})^{-2\sigma}\int_0^\infty y^{2\sigma-1}|J_0(y)|\dd y\), and
\(\int_0^\infty u^{r-d\sigma}\e^{-u}\dd u<\infty\).  Hence Fubini's
theorem applies, and with
\(\int_0^\infty y^{2z-1}J_0(y)\dd y=2^{2z-1}\Gamma(z)/\Gamma(1-z)\)
\cite[equation~(10.22.43)]{NISTHandbook2010} we obtain
\[
\int_0^\infty x^{z-1}g(x)\dd x
=\pi\,d^{2z}\,\frac{\Gamma(z)\,\Gamma(r+1-dz)}{\Gamma(1-z)} .
\]

\emph{Step 3: Gauss's multiplication formula.}  By
\cite[equation~(5.5.6)]{NISTHandbook2010}, applied at \(r+1-dz\) and at
\(r+1\),
\[
\frac{\Gamma(r+1-dz)}{\Gamma(r+1)}
=d^{-dz}\prod_{j=0}^{d-1}
\frac{\Gamma\bigl(\frac{r+1+j}{d}-z\bigr)}{\Gamma\bigl(\frac{r+1+j}{d}\bigr)}.
\]
The factor with \(j=d-1-r\) equals \(\Gamma(1-z)\).  Therefore
\[
\int_0^\infty x^{z-1}g(x)\dd x
=\pi\,r!\,\Gamma(z)\,\bigl(d^{\,d-2}\bigr)^{-z}
\prod_{j\in J_r}\frac{\Gamma(\beta_{r,j}-z)}{\Gamma(\beta_{r,j})}
=\pi\,r!\,\Gamma(z)\,\E\bigl[(d^{\,d-2}S_r)^{-z}\bigr].
\]

\emph{Step 4: identification.}  Let
\(\tilde g(x)=\pi r!\,\E[\exp(-x\,d^{\,d-2}S_r)]\).  By Tonelli's theorem
and \(\int_0^\infty x^{z-1}\e^{-xs}\dd x=\Gamma(z)s^{-z}\), the Mellin
transform of \(\tilde g\) is the last expression for
\(0<\operatorname{Re}z<\min_{j\in J_r}\beta_{r,j}\), a strip that
contains the line \(\operatorname{Re}z=\sigma\) of Step~2.  Both \(g\)
and \(\tilde g\) are continuous on \((0,\infty)\), and
\(x^{\sigma-1}g\), \(x^{\sigma-1}\tilde g\) are integrable.  Under
\(x=\e^s\), their Mellin transforms on \(\operatorname{Re}z=\sigma\) are
the Fourier transforms of the integrable functions \(\e^{\sigma s}g(\e^s)\)
and \(\e^{\sigma s}\tilde g(\e^s)\); these coincide, so \(g=\tilde g\).
\end{proof}

The representation also shows what happens at the endpoint \(a=0\) of
\cite[Conjecture~3.6]{FelderHoppe2025}.  For \(r\in\{0,\ldots,d-1\}\) let
\(j_r=\min J_r\), so that \(j_r=0\) for \(r\leq d-2\) and
\(j_{d-1}=1\), and let \(\beta_r=\beta_{r,j_r}=\min_{j\in J_r}\beta_{r,j}\).

\begin{corollary}[The endpoint \(a=0\)]\label{cor:endpoint}
For \(r\in\{0,\ldots,d-1\}\),
\[
\lim_{a\to0^+}a^{-j_r}\int_\C|z|^{2r}\rho_a\dd A
=\pi\,r!\,d^{-(d-2)\beta_r}\prod_{j\in J_r\setminus\{j_r\}}
\frac{\Gamma(\beta_{r,j}-\beta_r)}{\Gamma(\beta_{r,j})}
\in(0,\infty).
\]
Consequently, as \(a\to0^+\), the leading Gram matrices
\(\bigl[(z^p,z^q)_a\bigr]_{p,q=0}^N\) with \(N\leq d-2\) converge to
nonsingular diagonal matrices, while for \(N=d-1\) the limit is a
diagonal matrix of rank \(d-1\).
\end{corollary}

\begin{proof}
Write \(S_r=G_{r,j_r}R_r\) with \(R_r=\prod_{j\in J_r\setminus\{j_r\}}
G_{r,j}\) (an empty product is \(1\)), and let
\(\kappa=d^{\,d-2}a^{-d}\).  Conditioning on \(R_r\) and using
\(\E[\e^{-sG}]=(1+s)^{-\beta}\) for a Gamma variable \(G\) of shape
\(\beta\) and \(s\geq0\), Proposition~\ref{prop:gamma} gives
\(\int_\C|z|^{2r}\rho_a\dd A=\pi r!\,a^{-r-1}
\E[(1+\kappa R_r)^{-\beta_r}]\).  Since \(d\beta_r=r+1+j_r\), we have
\(\kappa^{\beta_r}=d^{(d-2)\beta_r}a^{-r-1-j_r}\), so
\[
a^{-j_r}\int_\C|z|^{2r}\rho_a\dd A
=\pi\,r!\,d^{-(d-2)\beta_r}\,
\E\left[\left(\frac{\kappa}{1+\kappa R_r}\right)^{\beta_r}\right].
\]
As \(a\to0^+\), \(\kappa\) increases to \(\infty\) and
\(\kappa/(1+\kappa R_r)\) increases to \(R_r^{-1}\).  By monotone
convergence the expectation tends to
\(\E[R_r^{-\beta_r}]=\prod_{j\in J_r\setminus\{j_r\}}
\Gamma(\beta_{r,j}-\beta_r)/\Gamma(\beta_{r,j})\), which is finite
because \(\beta_{r,j}>\beta_r\) for \(j\neq j_r\).

For \(N\leq d-1\) the monomials \(1,z,\ldots,z^N\) lie in distinct
weight spaces, so by \eqref{eq:gram-block} the Gram matrix is diagonal
with entries \((z^r,z^r)_a=(-1)^r\int_\C|z|^{2r}\rho_a\dd A\),
\(0\leq r\leq N\).  These have nonzero limits for \(r\leq d-2\), where
\(j_r=0\), and the entry with \(r=d-1\) is \(O(a)\).
\end{proof}

\section{Signs of the Hankel determinants}\label{sec:signs}

For real \(x_1,\ldots,x_k\) write
\(V(x_1,\ldots,x_k)=\prod_{1\leq i<j\leq k}(x_j-x_i)\).

\begin{lemma}[Hankel signs]\label{lem:hankel-signs}
Let \(m\geq1\), \(\beta_1,\ldots,\beta_m>0\) and \(\kappa>0\), let
\(G_1,\ldots,G_m\) be independent Gamma variables with shapes
\(\beta_1,\ldots,\beta_m\), and let
\(F(t)=\E[\exp(-\e^t\kappa G_1\cdots G_m)]\).  Then, for every real
\(t\) and every \(k\geq1\),
\[
(-1)^{\binom k2}\det\left[F^{(p+q)}(t)\right]_{p,q=0}^{k-1}>0.
\]
\end{lemma}

\begin{proof}
The variable \(\log G_j\) has the density
\(q_j(v)=\e^{\beta_jv-\e^v}/\Gamma(\beta_j)\) on \(\mathbb R\).  Put
\(\phi_0(u)=\exp(-\e^u)\) and, for \(j=1,\ldots,m\),
\[
\phi_j(u)=\E\bigl[\phi_{j-1}(u+\log G_j)\bigr]
=\int_{\mathbb R}\phi_{j-1}(w)\,q_j(w-u)\dd w,
\]
so that \(F(t)=\phi_m(t+\log\kappa)\).  By \eqref{eq:stirling} with
\(G(x)=\e^{-x}\),
\(\phi_0^{(p)}(u)=\e^{-x}\sum_i\stir pi(-x)^i\) with \(x=\e^u\); in
particular \(\phi_0^{(p)}\) is bounded.  By induction and dominated
convergence, each \(\phi_j\) is smooth with bounded derivatives
\(\phi_j^{(p)}(u)=\E[\phi_{j-1}^{(p)}(u+\log G_j)]
=\int\phi_{j-1}^{(p)}(w)q_j(w-u)\dd w\).

\emph{Claim: for \(0\leq j\leq m-1\) and \(u_1<\cdots<u_k\),}
\(\sgn\det[\phi_j^{(p)}(u_l)]_{p<k,\,l\leq k}=(-1)^{\binom k2}\).
For \(j=0\), the matrix \(\Sigma\) of Corollary~\ref{cor:hankel} is
unitriangular, so with \(x_l=\e^{u_l}\),
\[
\det[\phi_0^{(p)}(u_l)]
=\e^{-\sum_lx_l}\,V(-x_1,\ldots,-x_k)
=(-1)^{\binom k2}\e^{-\sum_lx_l}\,V(x_1,\ldots,x_k),
\]
and \(V(x)>0\) because the \(x_l\) increase.  For the induction step,
Andr\'eief's identity \cite{Andreief1886,Forrester2019}, applied to the
bounded functions \(\phi_{j-1}^{(p)}\) and the integrable functions
\(w\mapsto q_j(w-u_l)\), together with the symmetry of the integrand,
gives
\[
\det[\phi_j^{(p)}(u_l)]
=\int_{w_1<\cdots<w_k}
\det[\phi_{j-1}^{(p)}(w_i)]_{p,i}\,
\det[q_j(w_i-u_l)]_{i,l}\prod_i\dd w_i .
\]
Here \(q_j(w-u)=\Gamma(\beta_j)^{-1}\e^{\beta_jw}\e^{-\beta_ju}
\exp(\xi\zeta)\) with \(\xi=\e^w\) and \(\zeta=-\e^{-u}\), both strictly
increasing.  The kernel \(\exp(\xi\zeta)\) is strictly totally positive:
for \(\xi_1<\cdots<\xi_k\) and \(\zeta_1<\cdots<\zeta_k\),
\(\det[\e^{\xi_i\zeta_l}]>0\).  Indeed, a nonzero sum
\(\sum_lc_l\e^{\zeta_l\xi}\) has at most \(k-1\) real zeros, by induction
on \(k\) with Rolle's theorem applied to
\(\frac{\dd}{\dd\xi}(\e^{-\zeta_1\xi}\sum_lc_l\e^{\zeta_l\xi})\); so the
determinant never vanishes on the connected set of ordered
\((\xi,\zeta)\).  To find its sign, fix \(x_1<\cdots<x_k\) and put
\(\xi_i=\varepsilon x_i\).  Expanding
\(\e^{\varepsilon x_i\zeta_l}=\sum_{p\geq0}(\varepsilon x_i\zeta_l)^p/p!\) and
applying the Cauchy--Binet formula gives
\[
\det[\e^{\varepsilon x_i\zeta_l}]
=\varepsilon^{\binom k2}\,
\frac{V(x_1,\ldots,x_k)\,V(\zeta_1,\ldots,\zeta_k)}{\prod_{p=0}^{k-1}p!}
+O\bigl(\varepsilon^{\binom k2+1}\bigr)
\qquad(\varepsilon\downarrow0),
\]
which is positive for small \(\varepsilon\).  Hence the second determinant is
positive on the ordered region, the first has sign \((-1)^{\binom k2}\) by
induction, and the claim follows.

Now let \(u=t+\log\kappa\) and \(H_{pq}=\phi_m^{(p+q)}(u)\).  From
\(q_m'=q_m\cdot(\beta_m-\e^v)\), induction gives
\(q_m^{(q)}(v)=q_m(v)P_q(\e^v)\), where \(P_0=1\) and
\(P_{q+1}(y)=(\beta_m-y)P_q(y)+yP_q'(y)\), so that \(P_q\) has degree
\(q\) and leading coefficient \((-1)^q\).  On \(|u|\leq M\),
\(|q_m^{(q)}(w-u)|\leq C_{q,M}\e^{\beta_mw}(1+\e^w)^q\exp(-\e^{-M}\e^w)\),
which is integrable in \(w\).  Differentiating
\(\phi_m^{(p)}(u)=\int\phi_{m-1}^{(p)}(w)q_m(w-u)\dd w\) a further \(q\)
times in \(u\) therefore gives
\[
H_{pq}=\int_{\mathbb R}\phi_{m-1}^{(p)}(w)\,g_q(w)\dd w,
\qquad
g_q(w)=(-1)^qq_m^{(q)}(w-u)=q_m(w-u)\,\widetilde P_q(\e^{w-u}),
\]
with \(\widetilde P_q=(-1)^qP_q\) monic of degree \(q\).  Andr\'eief's
identity gives
\[
\det H=\int_{w_1<\cdots<w_k}
\det[\phi_{m-1}^{(p)}(w_i)]\,
\prod_iq_m(w_i-u)\;V\bigl(\e^{w_1-u},\ldots,\e^{w_k-u}\bigr)
\prod_i\dd w_i ,
\]
because \(\det[\widetilde P_q(y_i)]=V(y)\) for monic \(\widetilde P_q\).
On the ordered region \(V(\e^{w_i-u})>0\), and by the claim the
integrand has sign \((-1)^{\binom k2}\) and does not vanish.  Hence
\((-1)^{\binom k2}\det H>0\).
\end{proof}

\begin{proposition}[block determinants]
\label{prop:block-determinants}
For \(r\in\{0,\ldots,d-1\}\) and \(k\geq1\),
\(\sgn\Delta_k^{(r)}=(-1)^{rk+\binom k2}\).
\end{proposition}

\begin{proof}
By Proposition~\ref{prop:gamma},
\(F_r(t)=\pi r!\,a^{-r-1}F(t)\), where \(F\) is the function of
Lemma~\ref{lem:hankel-signs} for the \(m=d-1\geq1\) shapes
\(\beta_{r,j}\), \(j\in J_r\), and \(\kappa=d^{\,d-2}a^{-d}\).  Hence
\(\sgn\det[F_r^{(p+q)}(0)]=(-1)^{\binom k2}\), and
Corollary~\ref{cor:hankel} gives the claim.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:main}(i)]
By Proposition~\ref{prop:block-determinants}, every \(\Delta_k^{(r)}\)
is nonzero, so by Section~\ref{sec:gram} every leading Gram matrix is
nondegenerate and the polynomials \(P_n\) exist.  Let \(n=r+dj\).
Replacing \(z^n\) by \(P_n\) in the basis
\(z^r,z^{r+d},\ldots,z^{r+dj}\) is a unitriangular change of basis, and
orthogonality makes the new Gram matrix
\(\operatorname{diag}\bigl([G_{pq}^{(r)}]_{p,q=0}^{j-1},(P_n,P_n)_a\bigr)\).
Comparing determinants gives
\begin{equation}
(P_n,P_n)_a
=\frac{\Delta_{j+1}^{(r)}}{\Delta_j^{(r)}};
\label{eq:norm-delta-ratio}
\end{equation}
this Schur-complement identity uses only the nonvanishing of the
leading minors, not positive definiteness.  By
Proposition~\ref{prop:block-determinants} and \(\binom{j+1}2-\binom j2=j\),
\(\sgn(P_n,P_n)_a=(-1)^{r+j}\), which is \(\varrho(n)\) by
\eqref{eq:rho-block}.  Hence \(\fh_n=\varrho(n)(P_n,P_n)_a>0\).  The
last assertion is the identification at the end of
Section~\ref{sec:gram}.
\end{proof}

\begin{remark}
Unwinding the proof of Lemma~\ref{lem:hankel-signs} writes
\((-1)^{rk+\binom k2}\Delta_k^{(r)}\) as a \(k(d-1)\)-fold integral of a
positive function.  By \eqref{eq:norm-delta-ratio}, the norms
\(\fh_n\) and the ratios \(V_n\) can therefore be evaluated without the
cancellation inherent in the oscillatory moment determinants.
\end{remark}

\section{The recurrence}\label{sec:completion}

Let \(d\geq3\).  Define \(V_n=\fh_{n+1}/\fh_n\) for \(n\geq0\) and
\(V_j=0\) for \(j<0\).  By Theorem~\ref{thm:main}(i), \(V_n>0\) for
every \(n\geq0\).  We derive \eqref{eq:FH-recurrence}, following
\cite[Lemma~3.4 and equations~(3.1)--(3.3)]{FelderHoppe2025}.

If \(g\) has weight \(\ell\), then
\begin{equation}
\sigma(zg)=-\tau(\ell)z\,\sigma g.
\label{eq:sigma-multiplication}
\end{equation}
For \(\ell\leq d-2\) this follows from
\((-\eta)^{-\ell-1}\eta=-(-\eta)^{-\ell}\); for \(\ell=d-1\) the weight
returns to \(0\), and
\(\sigma(zg)=\eta z\,g(\eta z)=\eta(-\eta)^{d-1}z\,\sigma g
=(-1)^{d-1}\eta^dz\,\sigma g=-\tau(d-1)z\,\sigma g\).

Let \(L=\partial_z+\ii z^{d-1}\), where
\(\partial_z=\frac12(\partial_{\operatorname{Re}z}
-\ii\partial_{\operatorname{Im}z})\).  Since
\(\partial_z\overline{\sigma g(z)}=0\) and
\(\partial_z\rho_a(z)=(-a\bar z+\ii z^{d-1})\rho_a(z)\), integration by
parts in \eqref{eq:pairing}, with no boundary terms because of the
Gaussian decay, and \eqref{eq:sigma-multiplication} give, for \(g\) of
weight \(\ell\),
\begin{equation}
(Lf,g)_a
=a\int_{\C}f\,\bar z\,\overline{\sigma g}\,\rho_a\dd A
=-\tau(\ell)a(f,zg)_a.
\label{eq:ibp-pairing}
\end{equation}

The polynomials \(zP_n\) and \(LP_n\) have weights \(n+1\) and \(n-1\)
modulo \(d\), degrees \(n+1\) and \(n+d-1\), and leading coefficients
\(1\) and \(\ii\).  If \(j\leq n+1-2d\) and \(j\equiv n+1\pmod d\), then
\(\deg LP_j<n\), so \eqref{eq:ibp-pairing} gives
\(0=(LP_j,P_n)_a=-\tau(n)a(P_j,zP_n)_a\).  If \(j\leq n-1-d\) and
\(j\equiv n-1\pmod d\), then \(\deg zP_j<n\), so
\((LP_n,P_j)_a=-\tau(j)a(P_n,zP_j)_a=0\).  Hence
\begin{equation}
zP_n=P_{n+1}+c_nP_{n+1-d},
\qquad
LP_n=\ii P_{n+d-1}+d_nP_{n-1},
\label{eq:polynomial-recurrences}
\end{equation}
where terms with negative indices are omitted; equivalently,
\(c_n=0\) for \(n\leq d-2\), and \(c_n\) for \(n\geq d-1\) and \(d_n\)
for \(n\geq1\) are the coefficients displayed.  The \(d-1\) consecutive
integers \(n-d+1,\ldots,n-1\) miss exactly the residue of \(n\) modulo
\(d\), and the product of \(\tau\) over a full residue system is
\((-1)^{d-1}\); hence \eqref{eq:rho-sign} gives
\[
\varrho(n)=\tau(n)\varrho(n-d+1)\quad(n\geq d-1),
\qquad
\varrho(n)=-\tau(n-1)\varrho(n-1)\quad(n\geq1).
\]
Pairing \eqref{eq:polynomial-recurrences} with \(P_{n+1-d}\) (for
\(n\geq d-1\)) and \(P_{n-1}\) (for \(n\geq1\)), and using
\eqref{eq:ibp-pairing} and Hermitian symmetry, we obtain
\[
\begin{split}
\ii\varrho(n)\fh_n
&=(LP_{n+1-d},P_n)_a
=-\tau(n)a(P_{n+1-d},zP_n)_a,\\
c_n
&=\frac{(zP_n,P_{n+1-d})_a}{\varrho(n+1-d)\fh_{n+1-d}}
=\frac{\ii}{a}\frac{\fh_n}{\fh_{n+1-d}},\\
d_n
&=\frac{(LP_n,P_{n-1})_a}{\varrho(n-1)\fh_{n-1}}
=-\tau(n-1)a
\frac{(P_n,zP_{n-1})_a}{\varrho(n-1)\fh_{n-1}}
=a\frac{\fh_n}{\fh_{n-1}};
\end{split}
\]
the first line holds because the leading term of \(LP_{n+1-d}\) is
\(\ii P_n\), and the last because that of \(zP_{n-1}\) is \(P_n\).
Thus \(c_m=\frac{\ii}{a}\prod_{i=m+1-d}^{m-1}V_i\) for every \(m\geq0\),
including \(c_m=0\) for \(m\leq d-2\).

Applying the first relation in \eqref{eq:polynomial-recurrences}
\(d-1\) times to \(P_n\), a path from \(P_n\) to \(P_{n-1}\) in \(d-1\)
steps of \(+1\) or \(-(d-1)\) uses exactly one step of \(-(d-1)\).  So
the coefficient of \(P_{n-1}\) in \(z^{d-1}P_n\) is
\(\sum_{s=0}^{d-2}c_{n+s}\).  Let \(n\geq1\).  The coefficient of
\(P_{n-1}\) in \(\partial_zP_n\) is \(n\), since
\(\partial_zP_n=nz^{n-1}+\cdots\) lies in the weight space of
\(P_{n-1}\).  Comparing coefficients of \(P_{n-1}\) in
\(LP_n=\partial_zP_n+\ii z^{d-1}P_n\) and using \(d_n=aV_{n-1}\), we
obtain, with \(m=n-1\geq0\),
\[
aV_m=m+1-\frac1a\sum_{s=0}^{d-2}\ \prod_{i=m+s-d+2}^{m+s}V_i ,
\]
which is \eqref{eq:FH-recurrence}.

\begin{proof}[Proof of Theorem~\ref{thm:main}(ii)]
The sequence \(V_n=\fh_{n+1}/\fh_n\) is positive and satisfies
\eqref{eq:FH-recurrence}.  For \(j\leq d-1\), \(P_j=z^j\),
\(\sigma z^j=(-1)^jz^j\) by \eqref{eq:twist-sign}, and
\(\varrho(j)=(-1)^j\); hence \(\fh_j=\int_\C|z|^{2j}\rho_a\dd A\), and
\(V_j\) is given by \eqref{eq:FH-initial} for \(j\leq d-3\).  If
\((\widetilde V_n)\) is another real solution with these initial values
and \(\widetilde V_i=V_i\) for \(i\leq m+d-3\), then
\eqref{eq:FH-recurrence} at index \(m\) is linear in
\(\widetilde V_{m+d-2}\) with coefficient
\(a^{-2}\widetilde V_m\cdots\widetilde V_{m+d-3}=a^{-2}V_m\cdots V_{m+d-3}>0\),
so \(\widetilde V_{m+d-2}=V_{m+d-2}\).  Induction proves uniqueness.
\end{proof}

\section{The quartic case}\label{sec:quartic}

In this section \(d=4\).  Let \(y>0\), \(\alpha\geq0\), \(\beta\geq0\),
and \(b=\beta+\frac12\).  For \(w>0\), define
\begin{equation}
\Phi_{\alpha,\beta}(w;y)
=\int_0^\infty
\e^{-ys}s^{\alpha-1/2}(1+ws^2)^{-b}\dd s .
\label{eq:Phi}
\end{equation}
Throughout, \(y=a^2/2\) and \(C=\sqrt{\pi/2}\).

\begin{lemma}[quartic kernels]\label{lem:quartic-kernels}
Define
\begin{equation}
\begin{array}{c|c|c|c}
r&A_r&\alpha_r&\beta_r\\ \hline
0&C&0&0\\
1&aC&1&0\\
2&2C&1&1
\end{array}
\label{eq:block-parameters}
\end{equation}
Then \(\mathcal W_r(a;\lambda)=A_r\Phi_{\alpha_r,\beta_r}(\lambda^2;y)\)
for \(r=0,1,2\) and \(\lambda>0\).
\end{lemma}

\begin{proof}
Let \(\nu=\alpha+\frac12\).  Since \((1+ws^2)^{-b}=\E[\e^{-ws^2G_b}]\)
for a Gamma variable \(G_b\) with shape \(b\), and \(\e^{-ys}s^{\nu-1}\)
is \(\Gamma(\nu)y^{-\nu}\) times the density of \(G_\nu/y\),
\[
\Phi_{\alpha,\beta}(w;y)
=\Gamma(\nu)y^{-\nu}\,\E\left[\exp\bigl(-wy^{-2}G_\nu^2G_b\bigr)\right]
\]
with \(G_\nu\) and \(G_b\) independent.  By the duplication formula
\cite[equation~(5.5.5)]{NISTHandbook2010}, \(G_\nu^2\) has the same
Mellin transform, and hence the same law, as \(4G_{\nu/2}G_{(\nu+1)/2}\)
with independent factors.  So \(\Phi_{\alpha,\beta}(w;y)
=\Gamma(\nu)y^{-\nu}\E[\exp(-4wy^{-2}G_{\nu/2}G_{(\nu+1)/2}G_b)]\).  For
\((\alpha,\beta)=(\alpha_r,\beta_r)\) the shapes
\(\{\nu/2,(\nu+1)/2,b\}\) are \(\{\frac14,\frac34,\frac12\}\),
\(\{\frac34,\frac54,\frac12\}\) and \(\{\frac34,\frac54,\frac32\}\), which
are the shapes \(\beta_{r,j}\), \(j\in J_r\), of
Section~\ref{sec:gamma} for \(r=0,1,2\).  Moreover
\(4y^{-2}=16a^{-4}=d^{\,d-2}a^{-d}\) and
\(A_r\Gamma(\nu)y^{-\nu}=\pi r!\,a^{-r-1}\).  The claim follows from
Proposition~\ref{prop:gamma}.
\end{proof}

\begin{lemma}[Bessel form]\label{lem:bessel}
For every \(a>0\),
\(\int_\C\rho_a\dd A=h(a)\), the Bessel combination \eqref{eq:h-bessel}.
\end{lemma}

\begin{proof}
Put \(H(a)=\int_\C\rho_a\dd A\) and
\(m_{pq}=\int_\C z^p\bar z^q\rho_a(z)\dd A(z)\) for \(a>0\).

\emph{Step 1: \(H'''+a^2H'+aH=0\) on \((0,\infty)\).}  Differentiation
under the integral sign gives \(H^{(k)}(a)=(-1)^km_{kk}\).  With the
Wirtinger derivative
\(\partial_z=\frac12(\partial_{\operatorname{Re}z}-\ii\partial_{\operatorname{Im}z})\),
\(\partial_z\bar z^q=0\) and
\(\partial_z\rho_a=(-a\bar z+\ii z^3)\rho_a\), so integrating
\(\partial_z(z^p\bar z^q\rho_a)\) over \(\C\), with no boundary terms
because of the Gaussian decay, gives
\[
p\,m_{p-1,q}+\ii\,m_{p+3,q}=a\,m_{p,q+1}.
\]
For \((p,q)=(1,0)\) and \((0,3)\) this reads
\(m_{00}+\ii m_{40}=am_{11}\) and \(\ii m_{33}=am_{04}\).  The
substitution \(z\mapsto\eta z\) of Section~\ref{sec:gram} gives
\(\overline{m_{qp}}=\bar\eta^{\,p}\eta^q m_{pq}\); hence every
\(m_{kk}\) is real and \(\overline{m_{40}}=-m_{04}\).  Therefore
\(m_{33}=am_{00}-a^2m_{11}\), which is the claimed equation.

\emph{Step 2: the Bessel side.}  For \(x>0\),
\(J_\nu(x)=(x/2)^\nu s_\nu(x)\) with the even entire function
\(s_\nu(x)=\sum_{k\geq0}(-1)^kx^{2k}/\bigl(4^kk!\,\Gamma(k+\nu+1)\bigr)\)
\cite[equation~(10.2.2)]{NISTHandbook2010}, and Bessel's equation
\cite[equation~(10.2.1)]{NISTHandbook2010} becomes
\(xs_\nu''+(2\nu+1)s_\nu'+xs_\nu=0\).  Writing \(s_\pm=s_{\pm1/4}\) and
\(x=a^2/4\), so that \((x/2)^{\mp1/4}=(a^2/8)^{\mp1/4}\), we get, for
\(a>0\),
\[
h(a)=h_S(a):=\frac{\pi^2}{4}\left[\sqrt8\,s_-(x)^2
-\sqrt2\,a\,s_-(x)s_+(x)+\frac{a^2}{\sqrt8}\,s_+(x)^2\right].
\]
The function \(h_S\) is smooth on \(\mathbb R\).  Put
\(U(a)=s_-(a^2/4)\) and \(V(a)=a\,s_+(a^2/4)\).  The equations for
\(s_\mp\), with \(2\nu+1=\frac12\) and \(\frac32\), give
\(U''+\frac{a^2}{4}U=0\) and \(V''+\frac{a^2}{4}V=0\).  If
\(y_1,y_2\) solve \(y''+qy=0\), then \(P=y_1y_2\) satisfies
\(P'''+4qP'+2q'P=0\); with \(q=a^2/4\) this is
\(P'''+a^2P'+aP=0\).  Since
\(h_S=\frac{\pi^2}{4}\bigl(\sqrt8\,U^2-\sqrt2\,UV+V^2/\sqrt8\bigr)\),
we get \(h_S'''+a^2h_S'+ah_S=0\) on \(\mathbb R\).  Since
\(s_\nu(0)=1/\Gamma(\nu+1)\) and \(s_\nu'(0)=0\),
\[
h_S(0)=\frac{\pi^2\sqrt8}{4\,\Gamma(\frac34)^2},
\qquad
h_S'(0)=-\frac{\pi^2\sqrt2}{4\,\Gamma(\frac34)\Gamma(\frac54)},
\qquad
h_S''(0)=\frac{\pi^2}{2\sqrt8\,\Gamma(\frac54)^2}.
\]

\emph{Step 3: the planar side as \(a\to0^+\).}  By
Lemma~\ref{lem:quartic-kernels} with \(\lambda=1\),
\[
\begin{split}
H&=C\,\Phi_{0,0}(1;y),\\
H'&=-\mathcal W_1(a;1)=-aC\,\Phi_{1,0}(1;y),\\
H''&=\mathcal W_2(a;1)=2C\,\Phi_{1,1}(1;y).
\end{split}
\]
As \(y\downarrow0\), monotone convergence and
\(\int_0^\infty s^{2x-1}(1+s^2)^{-x-z}\dd s=\frac12B(x,z)
=\frac{\Gamma(x)\Gamma(z)}{2\Gamma(x+z)}\)
\cite[equations~(5.12.1) and (5.12.3)]{NISTHandbook2010} give
\(\Phi_{0,0}(1;y)\to\frac12B(\frac14,\frac14)=\Gamma(\frac14)^2/(2\sqrt\pi)\)
and \(\Phi_{1,1}(1;y)\to\frac12B(\frac34,\frac34)=\Gamma(\frac34)^2/\sqrt\pi\).
The substitution \(s=u/y\) gives
\(a\Phi_{1,0}(1;y)=\sqrt2\int_0^\infty\e^{-u}u^{1/2}(y^2+u^2)^{-1/2}\dd u\);
the integrand is bounded by \(\e^{-u}u^{-1/2}\), so by dominated
convergence this tends to \(\sqrt2\,\Gamma(\frac12)=\sqrt{2\pi}\).  Using
\(\Gamma(\frac14)\Gamma(\frac34)=\pi\sqrt2\),
\(\Gamma(\frac54)=\frac14\Gamma(\frac14)\) and \(\Gamma(\frac12)=\sqrt\pi\)
\cite[equations~(5.5.3), (5.5.1), (5.4.6)]{NISTHandbook2010}, the limits
of \(H\), \(H'\), \(H''\) as \(a\to0^+\) are \(h_S(0)\),
\(h_S'(0)=-\pi\) and \(h_S''(0)\).

\emph{Step 4: uniqueness.}  The function \(W=H-h_S\) is smooth on
\((0,\infty)\), satisfies \(W'''=-a^2W'-aW\), and \(W,W',W''\to0\) as
\(a\to0^+\).  Fix \(a_1>0\).  For \(0<a\leq a_1\), the energy
\(E=W^2+W'^2+W''^2\) satisfies \(E'\leq(2+a_1^2+a_1)E\), by
\(2|uv|\leq u^2+v^2\).  Hence \(\e^{-(2+a_1^2+a_1)a}E(a)\) is
nonincreasing on \((0,a_1]\) and tends to \(0\) as \(a\to0^+\), so
\(E=0\) there.  Thus \(H=h_S=h\) on \((0,\infty)\).
\end{proof}

The identity of Lemma~\ref{lem:bessel} also follows from
Lemma~\ref{lem:quartic-kernels} and the Dixon--Ferrar formula
\cite[entry~6.518]{GradshteynRyzhik2015}: substitute \(s=\sinh t\) in
\(\Phi_{0,0}(1;y)\), use
\(K_{1/2}(z)=\sqrt{\pi/(2z)}\,\e^{-z}\), take \(\nu=\frac14\) and
\(x=a^2/4\) in the formula, and use
\(Y_{1/4}=J_{1/4}-\sqrt2\,J_{-1/4}\).

\begin{proof}[Proof of Theorem~\ref{thm:quartic}]
With \(d=4\), \(V_m=av_m\) and \(\epsilon=a^{-2}\),
\eqref{eq:FH-recurrence} is \eqref{eq:quartic-recurrence}.  By
Lemma~\ref{lem:bessel}, \(h(a)=\int_\C\rho_a\dd A\), and differentiation
under this absolutely convergent integral gives
\(h'(a)=-\int_\C|z|^2\rho_a\dd A\) and
\(h''(a)=\int_\C|z|^4\rho_a\dd A\).  By the proof of
Theorem~\ref{thm:main}(ii),
\[
\fh_0=h,\qquad \fh_1=-h',\qquad \fh_2=h''.
\]
Hence \(h(a)>0\) and \(h'(a)<0\), so \eqref{eq:initial-values} is well
defined, and \(v_n=\fh_{n+1}/(a\fh_n)\) reproduces it.  Theorem~\ref{thm:main}(ii)
for \(d=4\) now gives existence, uniqueness and positivity.  (For
\(d=4\) the initial data of \eqref{eq:FH-initial} consist of \(V_0\) and
\(V_1\), that is, of \(v_0\) and \(v_1\).)
\end{proof}

\section{Uniqueness of the positive solution}\label{sec:unique}

Throughout this section \(d\geq3\) and \(\epsilon>0\) are fixed.  For a
positive sequence \((v_n)_{n\geq0}\), with \(v_k=0\) for \(k<0\), put
\(T_m=v_mv_{m+1}\cdots v_{m+d-2}\) for \(m\geq0\) and \(T_m=0\) for
\(m<0\); then \eqref{eq:general-recurrence} reads
\begin{equation}
v_n+\sum_{m=n-d+2}^{n}T_m=(n+1)\epsilon,
\qquad n\geq0.
\label{eq:integrated}
\end{equation}
For \(x,y>0\), the logarithmic mean is
\(\operatorname{LM}(x,y)=(y-x)/(\log y-\log x)\) if \(x\neq y\) and
\(\operatorname{LM}(x,x)=x\); it lies between \(x\) and \(y\), and
\begin{equation}
\operatorname{LM}(x,y)\geq\frac{x}{1+|\log(y/x)|}.
\label{eq:lm-lower}
\end{equation}
Indeed, this is clear if \(y\geq x\); if \(y=x\e^{-s}\) with
\(s>0\), then \(\operatorname{LM}(x,y)=x(1-\e^{-s})/s
\geq x/(1+s)\) because \(\e^s\geq1+s\).  For real numbers \(z_i\) and
\(h_i\) indexed by a finite set we use the identity
\begin{equation}
\Bigl(\sum_iz_i\Bigr)\Bigl(\sum_ih_i^2z_i\Bigr)
=\Bigl(\sum_ih_iz_i\Bigr)^2+\sum_{i<j}(h_i-h_j)^2z_iz_j .
\label{eq:square-identity}
\end{equation}

\begin{lemma}[crude bounds]\label{lem:crude}
Put \(K=1+(d-1)^{d-1}\epsilon^{d-2}\).  Every positive solution of
\eqref{eq:integrated} satisfies
\[
\frac{\epsilon}{K}(n+1)^{-(d-3)}\leq v_n\leq(n+1)\epsilon,
\qquad
T_n\leq(n+1)\epsilon
\qquad(n\geq0).
\]
\end{lemma}

\begin{proof}
All terms in \eqref{eq:integrated} are nonnegative, which gives the
upper bounds.  Factoring \(v_n\) out of \eqref{eq:integrated} leaves the
bracket \(1+\sum\prod v_i\), a sum over the \(d-1\) windows containing
\(n\) of the products of their other \(d-2\) entries.  Each such entry
has \(i\leq n+d-2\), so \(v_i\leq(i+1)\epsilon\leq(d-1)(n+1)\epsilon\),
and the bracket is at most
\(1+(d-1)\bigl((d-1)(n+1)\epsilon\bigr)^{d-2}\leq K(n+1)^{d-2}\).
\end{proof}

\emph{An approximate solution.}  For \(t>0\), let \(q(t)>0\) be the
root of \(q+(d-1)q^{d-1}=\epsilon t\); since the left-hand side is
increasing in \(q\), \(q\) is well defined, smooth and increasing.  Put
\(q_n=q(n+1)\), \(Q_m=q_mq_{m+1}\cdots q_{m+d-2}\) for \(m\geq0\),
\(Q_m=0\) for \(m<0\), and
\[
r_n=q_n+\sum_{m=n-d+2}^{n}Q_m-(n+1)\epsilon .
\]

\begin{lemma}[the approximate solution]\label{lem:reference}
For \(t\geq1\),
\(q(1)t^{1/(d-1)}\leq q(t)\leq\bigl(\epsilon t/(d-1)\bigr)^{1/(d-1)}\) and
\(q(1)\geq\epsilon/K\).  Moreover \(Q_m\leq(m+1)\epsilon\) and
\(|r_n|\leq4\epsilon(d-1)^4/(n+1)\) for all \(m,n\geq0\).
\end{lemma}

\begin{proof}
The upper bound follows from \((d-1)q^{d-1}\leq\epsilon t\).  For
\(x=q(1)t^{1/(d-1)}\) and \(t\geq1\),
\(x+(d-1)x^{d-1}\leq t\bigl(q(1)+(d-1)q(1)^{d-1}\bigr)=\epsilon t\), so
\(q(t)\geq x\).  For \(x=\epsilon/K\),
\(x+(d-1)x^{d-1}=\frac\epsilon K\bigl(1+(d-1)\epsilon^{d-2}K^{-(d-2)}\bigr)
\leq\epsilon\), so \(q(1)\geq\epsilon/K\).  By the upper bound,
\(Q_m\leq\epsilon(m+d-1)/(d-1)\leq(m+1)\epsilon\).

Let \(f=\log q\).  Differentiating \(q+(d-1)q^{d-1}=\epsilon t\) gives
\(f'=\epsilon/\bigl(q+(d-1)^2q^{d-1}\bigr)\), so \(0<f'(t)\leq1/t\), and
\[
f''=-f'^2\,\frac{1+(d-1)^3q^{d-2}}{1+(d-1)^2q^{d-2}},
\qquad
|f''(t)|\leq\frac{d-1}{t^2}.
\]
Let \(t=n+1\geq2(d-1)\).  For \(0\leq j\leq d-2\) and \(0\leq x\leq1\)
put \(P_j(x)=\prod_{k=0}^{d-2}q\bigl(t+x(k-j)\bigr)\); all arguments lie
in \([t/2,3t/2]\).  Since \(n\geq d-2\),
\(\sum_{m=n-d+2}^{n}Q_m=\sum_jQ_{n-j}=\sum_jP_j(1)\), while
\(\sum_jP_j(0)=(d-1)q(t)^{d-1}=\epsilon t-q(t)\) and
\(\sum_jP_j'(0)=q(t)^{d-1}f'(t)\sum_{j,k}(k-j)=0\).  Hence
\(r_n=\sum_j\bigl(P_j(1)-P_j(0)-P_j'(0)\bigr)\).  On \([t/2,3t/2]\) we have
\(f'\leq2/t\) and \(|f''|\leq4(d-1)/t^2\), so
\(|(\log P_j)'|\leq(d-1)^2/t\) and \(|(\log P_j)''|\leq4(d-1)^4/t^2\);
also \(P_j\leq q(3t/2)^{d-1}\leq3\epsilon t/(2(d-1))\).  Therefore
\(|P_j''|=P_j\,|(\log P_j)''+((\log P_j)')^2|\leq15\epsilon(d-1)^3/(2t)\),
and Taylor's formula gives
\(|r_n|\leq\frac12(d-1)\cdot15\epsilon(d-1)^3/(2t)\leq4\epsilon(d-1)^4/t\).
If \(t<2(d-1)\), then
\(-\epsilon t\leq r_n\leq\sum_{m=n-d+2}^{n}Q_m\leq(d-1)\epsilon t\),
and \((d-1)\epsilon t<4\epsilon(d-1)^3/t\).
\end{proof}

\begin{proposition}[a priori bound]\label{prop:apriori}
There is a constant \(M\), depending only on \(d\) and \(\epsilon\), such
that every positive solution of \eqref{eq:integrated} satisfies
\[
\sum_{n\geq0}\log^2\frac{v_n}{q_n}\leq M^2 .
\]
In particular \(v_n/q_n\to1\), and
\(v_n\bigl((d-1)/(\epsilon(n+1))\bigr)^{1/(d-1)}\to1\).
\end{proposition}

\begin{proof}
Put \(\delta_n=\log(v_n/q_n)\) and \(H(t)=\log K+(d-2)\log t\).  By
Lemmas~\ref{lem:crude} and~\ref{lem:reference}, both \(v_n\) and \(q_n\)
lie in \([\frac\epsilon K(n+1)^{-(d-3)},(n+1)\epsilon]\), so
\(|\delta_n|\leq H(n+1)\).  Let \(a_n=\operatorname{LM}(v_n,q_n)\),
\(b_m=\operatorname{LM}(T_m,Q_m)\) for \(m\geq0\), and
\(D_m=\sum_{i=m}^{m+d-2}\delta_i\).  Then \(v_n-q_n=a_n\delta_n\) and
\(T_m-Q_m=b_mD_m\), and subtracting the definition of \(r_n\) from
\eqref{eq:integrated} gives
\begin{equation}
a_n\delta_n+\sum_{m=\max(0,n-d+2)}^{n}b_mD_m=-r_n,
\qquad n\geq0.
\label{eq:linearized}
\end{equation}
By Lemmas~\ref{lem:crude} and~\ref{lem:reference},
\(0<b_m\leq(m+1)\epsilon\), and by \eqref{eq:lm-lower},
\begin{equation}
a_n\geq\frac{q_n}{1+|\delta_n|}
\geq\frac{q(1)(n+1)^{1/(d-1)}}{1+H(n+1)} .
\label{eq:log-means}
\end{equation}
Let \(h\) be real with finite support.  Multiplying
\eqref{eq:linearized} by \(h_n^2\delta_n\), summing over \(n\), collecting
the terms with the same \(b_m\), and using \eqref{eq:square-identity}, we
obtain
\begin{equation}
\sum_na_nh_n^2\delta_n^2
+\sum_mb_m\Bigl(\sum_{i=m}^{m+d-2}h_i\delta_i\Bigr)^2
=-\sum_nr_nh_n^2\delta_n
-\sum_mb_m\sum_{m\leq i<j\leq m+d-2}(h_i-h_j)^2\delta_i\delta_j .
\label{eq:localized}
\end{equation}
Let \(p=1/(4(d-1))\), \(w_n=(n+1)^{-p}\), and, for an integer \(R\geq1\),
\(h_n=(w_n-w_R)_+\), which is supported on \(n<R\).  Then \(h\leq w\) and,
for \(m\leq i<j\), \(|h_i-h_j|\leq|w_i-w_j|\leq p(j-i)(m+1)^{-p-1}\).  By
Lemma~\ref{lem:reference}, the first term on the right of
\eqref{eq:localized} is at most
\(B_1=4\epsilon(d-1)^4\sum_{t\geq1}t^{-1-2p}H(t)\).  Using
\(2|\delta_i\delta_j|\leq\delta_i^2+\delta_j^2\), \(|\delta_i|\leq H(m+d-1)\)
for \(i\leq m+d-2\), and the fact that a window has fewer than
\((d-1)^2/2\) pairs, each with \((j-i)^2\leq(d-1)^2\), the second term is
at most
\(B_2=\frac12\epsilon p^2(d-1)^4\sum_{m\geq0}(m+1)^{-1-2p}H(m+d-1)^2\).
Both series converge, and \(B=B_1+B_2\) depends only on \(d\) and
\(\epsilon\).  Dropping the squares on the left of \eqref{eq:localized},
\(\sum_na_nh_n^2\delta_n^2\leq B\) for every \(R\).  As \(R\to\infty\),
\(h_n\uparrow w_n\), and monotone convergence gives
\(\sum_na_nw_n^2\delta_n^2\leq B\).  By \eqref{eq:log-means} and
\(2p=1/(2(d-1))\),
\[
a_nw_n^2\geq\frac{q(1)(n+1)^{1/(2(d-1))}}{1+H(n+1)}\geq\frac{q(1)}{G},
\qquad
G=\sup_{t\geq1}\frac{1+H(t)}{t^{1/(2(d-1))}}<\infty,
\]
so \(\sum_n\delta_n^2\leq BG/q(1)=:M^2\).  Finally,
\((d-1)q(t)^{d-1}=\epsilon t-q(t)\) and \(q(t)/t\to0\) give
\(q(t)\bigl((d-1)/(\epsilon t)\bigr)^{1/(d-1)}\to1\).
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:unique}]
The asymptotic statement is part of Proposition~\ref{prop:apriori}.  Let
\(v\) and \(v'\) be positive solutions, with products \(T_m\) and
\(T_m'\), and put \(\eta_n=\log(v_n'/v_n)\).  By
Proposition~\ref{prop:apriori}, \(\eta\in\ell^2\).  With
\(A_n=\operatorname{LM}(v_n,v_n')>0\),
\(B_m=\operatorname{LM}(T_m,T_m')\leq(m+1)\epsilon\) and
\(E_m=\sum_{i=m}^{m+d-2}\eta_i\), subtracting the two copies of
\eqref{eq:integrated} gives
\(A_n\eta_n+\sum_{m=\max(0,n-d+2)}^{n}B_mE_m=0\), and the argument
leading to \eqref{eq:localized}, now without a source term, gives
\[
\sum_nA_nh_n^2\eta_n^2
\leq\sum_mB_m\sum_{m\leq i<j\leq m+d-2}(h_i-h_j)^2|\eta_i\eta_j|
\]
for finitely supported \(h\).  For an integer \(R\geq1\), take
\(h_n=1\) for \(n\leq R\),
\(h_n=2-n/R\) for \(R<n<2R\), and \(h_n=0\) for \(n\geq2R\).  Then
\(|h_i-h_j|\leq|i-j|/R\), and only windows with \(m<2R\) contribute, for
which \(B_m\leq2R\epsilon\).  A site lies in at most \(d-1\) windows, and
within a window \(\sum_{j\neq i}(j-i)^2\leq(d-1)^3\).  Hence
\[
\sum_nA_nh_n^2\eta_n^2
\leq\frac{2R\epsilon}{R^2}\cdot\frac{(d-1)^4}{2}\,\|\eta\|_{\ell^2}^2
=\frac{\epsilon(d-1)^4}{R}\|\eta\|_{\ell^2}^2 .
\]
For fixed \(n\) and \(R\geq n\), \(h_n=1\), so
\(A_n\eta_n^2\leq\epsilon(d-1)^4\|\eta\|_{\ell^2}^2/R\) for all large
\(R\).  Hence \(\eta_n=0\) for every \(n\), and \(v=v'\).  The last
assertions of the theorem follow from Theorems~\ref{thm:main}(ii)
and~\ref{thm:quartic}, since \(V_n=a^{2/(d-2)}v_n\) and
\(\epsilon=a^{-d/(d-2)}\) carry \eqref{eq:FH-recurrence} into
\eqref{eq:general-recurrence}.
\end{proof}

In the variables \(u_n=\log v_n\), \eqref{eq:integrated} is the
coordinatewise stationarity condition of the formal energy
\(\sum_n\bigl[\e^{u_n}+\e^{u_n+u_{n+1}+\cdots+u_{n+d-2}}-(n+1)\epsilon\,u_n\bigr]\),
whose increments along finitely supported variations are well defined
and strictly convex, and \eqref{eq:linearized} is a difference of its
gradients.  Convexity alone does not compare two infinite sequences.
In \eqref{eq:log-means} the convexity constant is controlled by the
known approximate solution \(q\), so it grows like \(n^{1/(d-1)}\) up to
a logarithm, whereas a direct comparison of two unknown solutions only
yields the much weaker lower bound of Lemma~\ref{lem:crude}.

\section*{AI-use disclosure}

The proof of the case \(d=4\) of Theorem~\ref{thm:main}, in an earlier
quartic-specific form, was developed with assistance from OpenAI Codex
using GPT-5.6 Sol (\texttt{gpt-5.6-sol}) at high and extra-high reasoning
effort.  The extension to every \(d\) (the Gamma representation and the
total-positivity argument of Sections~\ref{sec:gamma}
and~\ref{sec:signs}) was developed with assistance from Anthropic's
Claude Code using Claude Opus~5.5.  The manuscript was revised, and the
Lean formalization of the case \(d=4\) was produced, with assistance
from Claude Code using Claude Opus~5.5, Claude Fable~5 and Claude
Haiku~5.5; the Lean formalization for general \(d\) was produced with
assistance from Claude Code using Claude Opus~5.5.  The proof of Theorem~\ref{thm:unique}, by comparison
with an approximate solution, and the weighted energy estimate of an
earlier proof for \(d=4\) were obtained in consultations with OpenAI's
GPT-6 Pro, which was also used for independent referee-style checks of
the proofs, the citations and the Lean statements.  These systems were
used as interactive research assistants to develop and stress-test the
arguments, audit citations and calculations, write the formal proofs,
and revise the manuscript.  The author directed the research, selected
and checked the final arguments, and takes responsibility for all
mathematical claims, citations, computations, and wording.

\section*{Code availability}

The Lean~4 formalization of Theorems~\ref{thm:main}, \ref{thm:quartic}
and~\ref{thm:unique} and of Corollary~\ref{cor:endpoint} is in the
directory \path{lean} of release
\path{v2.3} of the repository
\href{https://github.com/skypher/painleve}{github.com/skypher/painleve}
(Lean~4.33.0, Mathlib commit \path{db584cd6d46c}).  The statements
\path{Painleve.Stmt_mainD} (Theorem~\ref{thm:main}),
\path{Painleve.Stmt_main} (the case \(d=4\) of Theorem~\ref{thm:main}
with Theorem~\ref{thm:quartic}), \path{Painleve.Stmt_uniqueD}
(Theorem~\ref{thm:unique}) and \path{Painleve.Stmt_endpoint}
(Corollary~\ref{cor:endpoint}) are proved by
\path{Painleve.main_theoremD}, \path{Painleve.main_theorem},
\path{Painleve.unique_theoremD} and \path{Painleve.endpoint_theorem}.
The proofs for general \(d\) follow
Sections~\ref{sec:gram}--\ref{sec:completion} and~\ref{sec:unique},
except that Proposition~\ref{prop:gamma} is proved there by comparing
characteristic functions (Gauss's multiplication formula in law for
logarithms of Gamma variables) instead of Mellin transforms.  The proof
of Theorem~\ref{thm:quartic}, and of the case \(d=4\) of the last
assertion of Theorem~\ref{thm:unique}, follows the quartic arguments of
the version of this paper in release \path{v1.1}.  These proofs use only
the axioms \path{propext}, \path{Classical.choice} and
\path{Quot.sound}; the repository README gives the build commands and
the file \path{lean/Check.lean} that checks them.  The directory
\path{runs/general-d} contains numerical checks of
Sections~\ref{sec:hankel}--\ref{sec:completion} for \(d\leq8\), and
\path{runs/uniq} the numerical scans of initial values used as a sanity
check for Theorem~\ref{thm:unique}.

\begin{thebibliography}{OLBC10}

\bibitem[AHK19]{ArnlindHoppeKontsevich2019}
J.~Arnlind, J.~Hoppe and M.~Kontsevich,
\emph{Quantum minimal surfaces},
\href{https://arxiv.org/abs/1903.10792}{arXiv:1903.10792} (2019).

\bibitem[And86]{Andreief1886}
C.~Andr\'eief,
\emph{Note sur une relation entre les int\'egrales d\'efinies des
produits des fonctions},
M\'em. Soc. Sci. Phys. Nat. Bordeaux (3) \textbf{2} (1886) 1--14.

\bibitem[Bor99]{Borodin1998}
A.~Borodin,
\emph{Biorthogonal ensembles},
Nucl. Phys. B \textbf{536} (1999) 704--732,
\href{https://doi.org/10.1016/S0550-3213(98)00642-7}%
{doi:\allowbreak 10.1016/S0550-3213(98)00642-7}.

\bibitem[CDHM25]{ClarksonEtAl2025}
P.~A.~Clarkson, A.~V.~Dzhamay, A.~N.~W.~Hone and B.~Mitchell,
\emph{Special solutions of a discrete Painlev\'e equation for quantum
minimal surfaces},
Theor. Math. Phys. \textbf{224} (2025) 1359--1397,
\href{https://doi.org/10.1134/S0040577925080045}%
{doi:\allowbreak 10.1134/S0040577925080045},
\href{https://arxiv.org/abs/2503.14436}{arXiv:2503.14436}.

\bibitem[CT99]{CornalbaTaylor1998}
L.~Cornalba and W.~Taylor~IV,
\emph{Holomorphic curves from matrices},
Nucl. Phys. B \textbf{536} (1999) 513--552,
\href{https://doi.org/10.1016/S0550-3213(98)00702-0}%
{doi:\allowbreak 10.1016/S0550-3213(98)00702-0}.

\bibitem[FH25]{FelderHoppe2025}
G.~Felder and J.~Hoppe,
\emph{Orthogonal polynomials with complex densities and quantum minimal
surfaces},
SIGMA \textbf{21} (2025) 103,
\href{https://doi.org/10.3842/SIGMA.2025.103}%
{doi:\allowbreak 10.3842/SIGMA.2025.103},
\href{https://arxiv.org/abs/2504.06197}{arXiv:2504.06197}.

\bibitem[For19]{Forrester2019}
P.~J.~Forrester,
\emph{Meet Andr\'eief, Bordeaux 1886, and Andreev, Kharkov 1882--1883},
Random Matrices Theory Appl. \textbf{8} (2019) 1930001,
\href{https://doi.org/10.1142/S2010326319300018}%
{doi:\allowbreak 10.1142/S2010326319300018},
\href{https://arxiv.org/abs/1806.10411}{arXiv:1806.10411}.

\bibitem[GR15]{GradshteynRyzhik2015}
I.~S.~Gradshteyn and I.~M.~Ryzhik,
\emph{Table of Integrals, Series, and Products},
8th ed., edited by D.~Zwillinger and V.~H.~Moll, Academic Press,
Amsterdam (2015).

\bibitem[Hop25]{Hoppe2025}
J.~Hoppe,
\emph{Quantum states from minimal surfaces},
\href{https://arxiv.org/abs/2502.18422}{arXiv:2502.18422} (2025).

\bibitem[OLBC10]{NISTHandbook2010}
F.~W.~J.~Olver, D.~W.~Lozier, R.~F.~Boisvert and C.~W.~Clark (eds.),
\emph{NIST Handbook of Mathematical Functions},
Cambridge University Press, New York (2010),
\href{https://dlmf.nist.gov/}{dlmf.nist.gov}.

\end{thebibliography}

\end{document}
