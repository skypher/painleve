# Positivity of the quartic solution of a discrete Painlevé-type recurrence

Paper and Lean 4 formalization.

- `paper.tex`, `paper.pdf`: the manuscript (Leslie P. Polzer). For `a > 0` it
  proves the `d = 4` case of the Felder–Hoppe Gram nondegeneracy conjecture
  (SIGMA 21 (2025) 103, Conjecture 3.6), positivity of the solution of the
  quartic recurrence with Bessel initial data (Theorem 1.1), and uniqueness
  of the positive solution (Theorem 1.2).
- `lean/`: a Lean 4 / Mathlib formalization of both theorems.
  - `Painleve/Statement.lean` and `Painleve/StatementUnique.lean` hold the
    frozen statements `Painleve.Stmt_main` and `Painleve.Stmt_unique`.
  - `Painleve.main_theorem : Painleve.Stmt_main` (in `Painleve/Main.lean`)
    and `Painleve.unique_theorem : Painleve.Stmt_unique` (in
    `Painleve/Unique.lean`) prove them, using only the axioms `propext`,
    `Classical.choice` and `Quot.sound`.
  - `LEDGER.md` maps the paper's lemmas to the Lean modules.
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
prints their axioms. The expected output is

```
'Painleve.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Painleve.unique_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The paper cites release `v1.1` of this repository. (Tag `v1.0` was
pushed by mistake on the commit before the final review fixes; use `v1.1`.)

`runs/uniq/` contains the numerical scans of initial values used as a sanity
check for Theorem 1.2.
