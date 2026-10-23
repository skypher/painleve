# Positive solutions of the Felder–Hoppe recurrences for quantum minimal surfaces

Paper and Lean 4 formalization.

- `paper.tex`, `paper.pdf`: the manuscript (Leslie P. Polzer). For every
  `d ≥ 2` and `a > 0` it proves the Felder–Hoppe Gram nondegeneracy
  conjecture (SIGMA 21 (2025) 103, Conjecture 3.6), with positive signed
  norms, and the positivity of the solution of their recurrence with moment
  initial data (Theorem 1.1). For `d = 4` it identifies the initial data with
  Bessel functions (Theorem 1.2) and proves that the positive solution is
  unique (Theorem 1.3).
- `general_d.md`: the working note for the general-`d` argument.
- `lean/`: a Lean 4 / Mathlib formalization of the case `d = 4`
  (Theorem 1.1 for `d = 4` with Theorem 1.2, and Theorem 1.3). It follows
  the quartic argument of the paper as of release `v1.1`; section and lemma
  numbers in its docstrings and in `LEDGER.md` refer to that version.
  - `Painleve/Statement.lean` and `Painleve/StatementUnique.lean` hold the
    frozen statements `Painleve.Stmt_main` and `Painleve.Stmt_unique`.
  - `Painleve.main_theorem : Painleve.Stmt_main` (in `Painleve/Main.lean`)
    and `Painleve.unique_theorem : Painleve.Stmt_unique` (in
    `Painleve/Unique.lean`) prove them, using only the axioms `propext`,
    `Classical.choice` and `Quot.sound`.
  - `LEDGER.md` maps the lemmas of the `v1.1` paper to the Lean modules.
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

`Check.lean` type-checks both theorems against the frozen statements and
fails unless their axioms are among `propext`, `Classical.choice` and
`Quot.sound`. The expected output is

```
Painleve.main_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
Painleve.unique_theorem: allowed axioms [propext, Classical.choice, Quot.sound]
```

GitHub CI (`.github/workflows/lean.yml`) builds the library and runs
`Check.lean` on every push and pull request.

The paper cites release `v2.0` of this repository (release `v1.1` holds the
earlier quartic-only version of the paper).

`runs/general-d/` contains the numerical checks of the general-`d` argument,
and `runs/uniq/` the numerical scans of initial values used as a sanity
check for Theorem 1.3.
