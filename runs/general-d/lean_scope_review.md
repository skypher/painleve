## Verdict: MINOR CHANGES

**There is no coverage overclaim for the four named results.** The required changes concern the description of proof routes and the scope of the acceptance check, not the frozen theorem statements.

This assessment uses the supplied source and the stipulated successful build/check output; it does not independently certify release history, source counts, or AI-use provenance.

| Item | Result | Reason |
|---|---|---|
| 1. Coverage | **PASS** | All conclusions of the four results are represented, including well-definedness and consequence clauses. |
| 2. Routes | **FAIL — minor** | The main route descriptions are correct, but the “except that” qualification omits other documented differences, particularly the weaker intermediate residual estimate. |
| 3. Consistency | **PASS** | Names, paths, release references, and the five checked declarations agree. Historical statement numbering is explainable, not a mathematical mismatch. |
| 4. Wording | **FAIL — minor** | Clarify the route exceptions, historical theorem numbering, and the distinction between audited proof dependencies and deliberate negative tests in `Check.lean`. |

## 1. Coverage

| Paper result | Comparison with the frozen statement |
|---|---|
| **Theorem 1.1 — `Stmt_mainD`** | Correct quantifiers: \(d\ge2\), \(a>0\), with part (ii) restricted to \(d\ge3\). It asserts every leading determinant is nonzero, positive signed norms, existence and uniqueness of the monic orthogonal polynomials, and identification of their norms. Part (ii) explicitly gives nonzero initial denominators, existence and uniqueness **among all real sequences with the prescribed initial data**, positivity, and the norm-ratio formula. |
| **Theorem 1.2 — `Stmt_main`** | Includes nonvanishing of \(h\) and \(h'\), the specified Bessel initial values, existence and uniqueness among real solutions, positivity, and \(v_n=\mathfrak h_{n+1}/(a\mathfrak h_n)\). It also includes the quartic Gram/norm assertions. The general statement `Stmt_mainD` independently covers the complete \(d=4\) instance of Theorem 1.1. |
| **Theorem 1.3 — `Stmt_uniqueD`** | Includes the exact asymptotic limit for arbitrary \(d\ge3\), \(\epsilon>0\), and every positive solution, together with uniqueness without prescribed initial data. Both “in particular” conclusions are present: the norm-ratio sequence is the unique positive FH solution, and a positive solution with the Bessel initial values is the unique positive quartic solution. |
| **Corollary 4.2 — `Stmt_endpoint`** | Includes the explicit constant, strict positivity, the right-hand limit, and both matrix consequences. The indexing is correct: Lean’s matrix size is \(n=N+1\), so `n < d` covers \(N\le d-2\), while size `d` covers \(N=d-1\). Exact rank \(d-1\), not merely singularity, is asserted. |

**The derivative well-definedness is not a gap.** Although `Stmt_main` does not explicitly contain `DifferentiableAt`, its nonzero first derivative implies differentiability. Moreover, existence of a solution with \(v_1>0\) forces `deriv (deriv hBessel) a ≠ 0`, hence differentiability of the first derivative. This uses Mathlib’s convention that a nonexistent derivative is assigned zero, confirmed in the pinned commit. [1]

No weakening of the introduction’s “formally verified” sentence is required.

## 2. Routes

The principal descriptions are supported:

- `GammaLaw` and `GammaRep` use characteristic functions of logarithmic Gamma laws, followed by integration of the exponential factor, rather than the paper’s Mellin-transform identification.
- The supplied `unique_theoremD` assembly explicitly uses `main_theorem` and `unique_theorem` for its final Bessel-solution conclusion. Its general normalized asymptotics and uniqueness—including \(d=4\)—come from `asymptoticsD` and `uniquenessD`.

However, the docstrings identify **three further differences**: `Endpoint` uses dominated rather than monotone convergence; `ExpTP` fixes the determinant sign by deformation to a Vandermonde matrix rather than the paper’s small-parameter expansion; and `UniqD3` uses residual constant **6**, whereas Lemma 8.2 states **4**.

These do not weaken any of the four final results. Nevertheless, the route description should distinguish following the paper’s **overall strategy** from reproducing every intermediate statement and proof. In particular, the LEDGER mapping must not suggest that the exact constant-4 version of Lemma 8.2 has been verified.

## 3. Consistency

The supplied check covers exactly these five declarations, all in namespace `Painleve`:

`main_theorem`, `unique_theorem`, `main_theoremD`, `endpoint_theorem`, and `unique_theoremD`.

It type-checks each against its named statement and checks its transitive axiom dependencies. The paper names four of these; saying the check verifies “them” is not false, but an explicit mention of the fifth would be clearer.

Release `v2.3` is consistent across the passages. `StatementD.lean` referring to the unchanged mathematical statements of `v2.2` is not a contradiction. Likewise, the older quartic theorem numbering is historical; do **not** modify frozen statements merely to update their comments. The README paths are correctly understood relative to `lean/`.

The added AI-use sentence is consistent with the LEDGER’s attribution to the main Claude Code session. Its historical truth is not something the theorem checks establish.

## 4. Wording

Required clarifications:

- Replace ambiguous “proved **there**” with “proved **in Lean**.”
- Replace the redundant “case \(d=4\) of the last assertion” with “final Bessel-solution assertion.”
- Include **theorem** numbers in the README’s historical-numbering qualification.
- Replace or explicitly scope the LEDGER’s source-purity claim. `Check.lean` deliberately contains `axiom unwanted` and a declaration using `sorryAx`; neither contaminates the five accepted theorems. The supplied acceptance output establishes dependency purity, not file counts, line counts, or absence of particular source tokens.

## Required replacement text

### `paper.tex`

Replace the passage from “The proofs for general \(d\) follow” through “that checks them.” Leave the preceding theorem mappings, introduction sentence, and AI-use addition unchanged.

:::writing{variant="document" id="67384" title="paper.tex — proof routes and acceptance check"}
The general-\(d\) formal proofs follow the overall strategy of
Sections~\ref{sec:gram}--\ref{sec:completion} and~\ref{sec:unique},
with some implementation differences.  In Lean,
Proposition~\ref{prop:gamma} is proved by comparing characteristic
functions of logarithms of Gamma variables, using Gauss's
multiplication formula in law, instead of Mellin transforms.
The endpoint argument uses dominated rather than monotone convergence;
the strict-total-positivity argument fixes the determinant sign by
deformation to a Vandermonde matrix; and the residual estimate
corresponding to Lemma~\ref{lem:reference} uses the constant \(6\)
instead of \(4\).  These differences do not change the four final
statements listed above.

The declarations \path{Painleve.main_theorem} and
\path{Painleve.unique_theorem} retain the quartic arguments of release
\path{v1.1}.  The former includes Theorem~\ref{thm:quartic}, and
\path{Painleve.unique_theoremD} invokes these two declarations for its
final Bessel-solution assertion.  Its asymptotic and uniqueness
assertions for the normalized recurrence, including \(d=4\), use the
general-\(d\) argument.

The file \path{lean/Check.lean} type-checks the four declarations
listed above against their statements, together with
\path{Painleve.unique_theorem : Painleve.Stmt_unique}, and checks
their transitive axiom dependencies.  Each of these five theorems
depends only on \path{propext}, \path{Classical.choice} and
\path{Quot.sound}.  The repository README gives the build commands.
:::

### `README.md`

Replace the general-`d` route sentences and the quartic route/numbering sentences, respectively, with these two paragraphs. Retain the existing declaration and file mappings.

:::writing{variant="document" id="29175" title="README.md — route descriptions"}
These general-`d` proofs follow the overall strategy of Sections 2–6 and 8 of the current paper, with implementation differences. Proposition 4.1 is proved using characteristic functions of logarithmic Gamma laws and Gauss's multiplication formula in law, rather than Mellin transforms. The endpoint argument uses dominated rather than monotone convergence, the strict-total-positivity argument fixes the determinant sign by deformation to a Vandermonde matrix, and the residual estimate corresponding to Lemma 8.2 uses constant 6 instead of 4. These differences do not change the final statements.

These quartic proofs follow the arguments of release `v1.1`; theorem, section and lemma numbers in their docstrings refer to that version. `Painleve.unique_theoremD` uses `Painleve.main_theorem` and `Painleve.unique_theorem` for its final Bessel-solution assertion. Its general normalized asymptotic and uniqueness assertions, including `d = 4`, use the general-`d` argument.
:::

### `lean/LEDGER.md`

Replace the acceptance paragraph with the following. The added second paragraph qualifies the existing module-mapping table without changing the frozen files.

:::writing{variant="document" id="84602" title="lean/LEDGER.md — acceptance scope and intermediate estimate"}
Acceptance: `lake env lean Check.lean` type-checks all five theorems against their frozen statements and checks their transitive axiom dependencies. Each depends only on `propext`, `Classical.choice` and `Quot.sound`. The acceptance harness deliberately includes an unwanted axiom and a declaration using `sorryAx` as negative regression tests; neither is a dependency of any accepted theorem. This acceptance check is a type and dependency audit, not a source-token, file-count or line-count audit.

The module mapping below records correspondence with the paper's arguments, not literal identity of every intermediate statement. In particular, `UniqD3` proves the residual estimate with constant 6 instead of the constant 4 in Lemma 8.2. This weaker intermediate estimate suffices for the stated asymptotic and uniqueness results.
:::

The same edits can be formatted as a unified diff for patch application.

Sources:
[1] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/Analysis/Calculus/Deriv/Basic.lean

