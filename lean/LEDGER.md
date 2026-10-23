# Lean formalization ledger

Final theorem: `Painleve.Stmt_main` (`Painleve/Statement.lean`), the Lean form
of Theorem 1.1 of `paper.tex` (part (i): Felder–Hoppe Conjecture 3.6 for
d = 4, a > 0, with positive signed norms; part (ii): Bessel initial data,
unique extension, positivity, and v_n = 𝔥_{n+1}/(a 𝔥_n)).

Acceptance check: `example : Painleve.Stmt_main := Painleve.main_theorem`
compiles with `#print axioms` showing only `propext`, `Classical.choice`,
`Quot.sound`.

Statement status: frozen 2026-10-23; independent statement check pending
(GPT-6 Pro via pro-cli).

Toolchain: Lean v4.33.0, Mathlib db584cd (same pin as `~/yang.lean`).

## Spine (paper source → Lean consumer)

| # | Paper item | Lean module (planned) | Consumer | Status |
|---|---|---|---|---|
| 1 | §2: twist on monomials `eq:twist-sign`, weight orthogonality, Gram blocks `eq:gram-block`, Hermitian symmetry | `Gram.lean` | 2, 7 | open |
| 2 | §2 + Cor 4.5: leading Gram matrix block-triangular by residue (`Matrix.BlockTriangular.det`), monic orthogonal P_n, `(P_n,P_n) = Δ_{j+1}/Δ_j` | `OrthoPoly.lean` | 6 | open |
| 3 | Lemma 3.1 (`lem:leading-source-signs`): one-sided scaling, `D = TBΛ` | `SignLemma.lean` | 5 | open |
| 4 | Lemma 3.1, `eq:andreief`: Andréief identity and positivity of det B | `Andreief.lean` | 3 | open |
| 5 | Lemma 4.1 (`lem:positive-source`, second equality), Lemma 4.2 (`lem:four-kernels`) | `Source.lean` | 6 | open |
| 6 | Lemma 4.3 (`lem:source-moments`), Prop 4.4, Cor 4.5 | `Blocks.lean` | 8 | open |
| 7 | §5: IBP pairing, banded expansions, recurrence `eq:V-recurrence`, uniqueness | `Recurrence.lean` | 8 | open |
| 8 | Lemma 4.1 for λ = 1: `hBessel = ∫ρ_a` | `BesselMatch.lean` | 9 | open |
| 9 | Theorem 1.1 assembly | `Main.lean` | final | open |

## Route notes (Lean vs paper)

- Item 6: the paper proves Lemma 4.3 through the radial J₀ representation and
  disk truncations. Lean plan: same statement via the Gaussian subordination
  of Lemma 4.1 (for each σ > 0 the two-source Gaussian integral converges for
  |u − v| < 4σ, with value π(σ² + uv/4)^{-1/2}); this avoids defining J₀.
  If adopted, mirror the argument into the paper so the two agree.
- Item 8: the paper cites the Dixon–Ferrar formula (G&R 6.518). Lean plan:
  both `hBessel` and `C Φ_{0,0}(1; a²/2)` solve `h''' + a² h' + a h = 0`, and
  their values of h, h′, h″ as a → 0⁺ are `C·B(1/4,1/4)/2`, `−π`,
  `C·B(3/4,3/4)` (checked numerically to ~10 digits, 2026-10-23); linear ODE
  uniqueness gives equality. Mirror into the paper if adopted.

## Reuse survey (Yang–Mills Lean, 2026-10-23)

No importable infrastructure for this project (fractional Bessel, Andréief,
indefinite orthogonal polynomials, ℂ integration by parts, Beta integrals are
absent). Patterns worth copying: `HermiteScale.lean`
(`paperPolynomialGaussianIntegrable`, Gaussian integration by parts),
`CB182L.lean` (Cauchy product of Bessel-type series),
`FAM088Core3.lean` (polar-coordinate wrappers).
