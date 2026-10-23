# Positive solutions of the Felder–Hoppe recurrences for quantum minimal surfaces

Paper and Lean 4 formalization.

- `paper.tex`, `paper.pdf`: the manuscript (Leslie P. Polzer). For every
  `d ≥ 2` and `a > 0` it proves the Felder–Hoppe Gram nondegeneracy
  conjecture (SIGMA 21 (2025) 103, Conjecture 3.6), with positive signed
  norms, and the positivity of the solution of their recurrence with moment
  initial data (Theorem 1.1). For `d = 4` it identifies the initial data with
  Bessel functions (Theorem 1.2). For every `d ≥ 3` it proves that the
  positive solution is unique and grows like `((n+1)ε/(d−1))^{1/(d−1)}`
  (Theorem 1.3). Corollary 4.2 shows that the range `a > 0` cannot be
  extended to `a = 0` by continuity: as `a → 0+`, the Gram matrix of
  order `d` converges to a matrix of rank `d − 1`.
- `general_d.md`: the working note for the general-`d` argument.
- `lean/`: a Lean 4 / Mathlib formalization of Theorems 1.1, 1.2 and 1.3
  and Corollary 4.2.
  - `Painleve/StatementD.lean` holds the frozen general-`d` statements
    `Painleve.Stmt_mainD` (Theorem 1.1), `Painleve.Stmt_uniqueD`
    (Theorem 1.3) and `Painleve.Stmt_endpoint` (Corollary 4.2), proved by
    `Painleve.main_theoremD` (`Painleve/MainD.lean`),
    `Painleve.unique_theoremD` (`Painleve/UniqueD.lean`) and
    `Painleve.endpoint_theorem` (`Painleve/Endpoint.lean`). These proofs
    follow the overall strategy of Sections 2–6 and 8 of the current
    paper, with implementation differences. Proposition 4.1 is proved
    using characteristic functions of logarithmic Gamma laws and Gauss's
    multiplication formula in law, rather than Mellin transforms. The
    proof of Corollary 4.2 uses dominated rather than monotone
    convergence, the total-positivity step of Lemma 5.1 fixes the
    determinant sign by deformation to a Vandermonde determinant, and the
    residual bound of Lemma 8.2 is proved with constant 6 instead of 4.
    These differences do not change the final statements.
  - `Painleve/Statement.lean` and `Painleve/StatementUnique.lean` hold the
    frozen `d = 4` statements `Painleve.Stmt_main` (Theorem 1.1 for `d = 4`
    with Theorem 1.2) and `Painleve.Stmt_unique` (uniqueness of the positive
    solution for `d = 4`), proved by `Painleve.main_theorem`
    (`Painleve/Main.lean`) and `Painleve.unique_theorem`
    (`Painleve/Unique.lean`). These follow the quartic arguments of
    release `v1.1`; theorem, section and lemma numbers in their docstrings
    refer to that version. `Painleve.unique_theoremD` uses
    `Painleve.main_theorem` and `Painleve.unique_theorem` for its final
    Bessel-solution assertion; its asymptotic and uniqueness assertions for
    the normalized recurrence, including `d = 4`, use the general-`d`
    argument.
  - All five theorems use only the axioms `propext`, `Classical.choice` and
    `Quot.sound`.
  - `LEDGER.md` maps the paper's results to the Lean modules.
  - `Check.lean` is the acceptance check (see below).

## Building

Paper: `pdflatex paper && pdflatex paper`.

Lean (toolchain `leanprover/lean4:v4.33.0`, Mathlib pinned in
`lean/lake-manifest.json`):

```
cd lean
lake exe cache get
lake build
```

To check the theorems and their axioms, run from `lean/` after the build:

```
lake env lean Check.lean
```

`Check.lean` type-checks the five theorems against the frozen statements
and fails unless their axioms are among `propext`, `Classical.choice` and
`Quot.sound`. The expected output is

```
Painleve.main_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.unique_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.main_theoremD: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.endpoint_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.unique_theoremD: allowed axioms [propext, Classical.choice, Quot.sound]
```

GitHub CI (`.github/workflows/lean.yml`) builds the library and runs
`Check.lean` on every push and pull request.

The paper cites release `v2.4` of this repository (release `v1.1` holds the
earlier quartic-only version of the paper).

`runs/general-d/` contains the numerical checks of the general-`d` argument,
and `runs/uniq/` the numerical scans of initial values used as a sanity
check for Theorem 1.3.
