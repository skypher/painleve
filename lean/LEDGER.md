# Lean formalization ledger

Final theorem: `Painleve.Stmt_main` (`Painleve/Statement.lean`), the Lean form
of Theorem 1.1 of `paper.tex` (part (i): Felder–Hoppe Conjecture 3.6 for
d = 4, a > 0, with positive signed norms; part (ii): Bessel initial data,
unique extension, positivity, and v_n = 𝔥_{n+1}/(a 𝔥_n)).

Acceptance check: `example : Painleve.Stmt_main := Painleve.main_theorem`
compiles with `#print axioms` showing only `propext`, `Classical.choice`,
`Quot.sound`.

Statement status: frozen 2026-10-23; APPROVED by independent statement check
(GPT-6 Pro via pro-cli, job_546a2722, all knobs PASS, no junk-value hazard).

Agents: user authorized up to 5 Haiku agents at high effort (2026-10-23).
Lanes work in /home/yang/painleve-scratch/<lane>/; main verifies and lands.

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

## Status: COMPLETE (2026-10-23)

`Painleve.main_theorem : Painleve.Stmt_main` (Painleve/Main.lean).
Acceptance check passed: `example : Painleve.Stmt_main := Painleve.main_theorem`
compiles; `#print axioms Painleve.main_theorem` = [propext, Classical.choice,
Quot.sound]; no `sorry`, `admit`, `axiom` or `native_decide` in the 34
modules (7522 lines). Statement.lean is byte-identical to the version the
independent statement check approved (commit de9c8b9).

Proof map: Gram blocks (Gram, BlockAlg) → Hankel identity in exponential
coordinates (DiskSource, DiskHankel, PlaneHankel) → kernels (Source = Lemma
4.1, Weighted = Lemma 4.2, Phi) → Hankel determinant (PhiHankel = Lemma 3.1,
Andreief, BiMoment) → block signs (BlockSign, Blocks = Prop 4.4) →
nondegeneracy and orthogonal polynomials (OrthoPoly, Assembly = Cor 4.5) →
recurrence (Herm, Ibp, Recurrence = Section 5) → Bessel initial data
(BesselSeries, HSeries, PlanarOde, Limits, OdeUnique, BesselMatch) → MainOf,
Main.

## Route for Lemmas 3.1 and 4.3 in Lean (one-variable calculus only)

Exponential coordinates u = e^{t₁}, v = e^{t₂}. On a disk of radius R the
two-source integral depends only on uv (`diskSource_eq_mul`: entire in a
complex shift s, invariant under imaginary shifts by rotation, hence
constant). So the matrix E^R_{pq} = Σ_{k,l} S(p,k) S(q,l) (i/4)^{k+l} M^R_{kl}
(S = Stirling numbers of the second kind) is Hankel: E^R_{pq} = F_R^{(p+q)}(0)
with F_R(t) the equal-coupling disk integral at coupling e^{t/2}. Let R → ∞
(dominated convergence; `iteratedDeriv_integral`). Full plane:
F_r(t) = A_r Φ_{α_r,β_r}(e^t; a²/2) (Lemma 4.1 with λ = e^{t/2}, Lemma 4.2).
Hankel sign: F^{(p+q)}(0) = Σ_j S(q,j) ∂_t^p[e^{jt}Φ^{(j)}(e^t)](0) and
e^{jt}Φ^{(j)}(e^t) = (−1)^j (b)_j e^{−γt} B_{0j}(y e^{−t/2}), so
H = T B Λ Sᵀ with T lower triangular, T_pp = (y/2)^p (`iteratedDeriv_scaling`).
det D = det E = det H gives Proposition 4.4's sign. This replaces the paper's
J₀ radial source and two-variable derivatives; mirror into the paper once
the Lean proof lands.

## Route notes (Lean vs paper)

- Item 6: superseded by the exponential-coordinate route above.
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
