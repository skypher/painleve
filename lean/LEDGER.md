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

## Proof map (paper item → Lean modules), final

| Paper item | Lean modules |
|---|---|
| §2: twist on monomials, weight orthogonality, Gram blocks, Hermitian symmetry | `Gram`, `BlockAlg` |
| Lemma 3.1 (Hankel determinant identity): scaling, `H = TBΛΣᵀ`, Andréief | `Phi`, `PhiHankel`, `Andreief`, `BiMoment` |
| Lemma 4.1 (positive source) | `Subord`, `Source` |
| Lemma 4.2 (four positive kernels) | `Weighted`, `Kernel` |
| Lemma 4.3 (Gram blocks in exponential coordinates) | `DiskSource`, `DiskHankel`, `PlaneHankel`, `Moments`, `DiffInt` |
| Proposition 4.4 (block determinants) | `BlockSign`, `Blocks`, `Signs` |
| Corollary 4.5 (nondegeneracy, signed norms) | `OrthoPoly`, `Assembly` |
| Lemma 5.1 (Bessel form) | `BesselSeries`, `HSeries`, `PlanarOde`, `Limits`, `OdeUnique`, `BesselMatch` |
| §6 (recurrence identification, uniqueness given initial data) | `Herm`, `Ibp`, `Recurrence`, `Uniq`, `Calc` |
| Theorem 1.1 assembly | `MainOf`, `Main` |
| §7, Theorem 1.2 | `UniqBounds`, `Energy`, `Unique` |

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
recurrence (Herm, Ibp, Recurrence = Section 6) → Bessel initial data
(BesselSeries, HSeries, PlanarOde, Limits, OdeUnique, BesselMatch = Lemma
5.1) → MainOf, Main.

## Theorem 1.2 (uniqueness of the positive solution): COMPLETE, 2026-10-23

`Painleve.unique_theorem : Painleve.Stmt_unique` (Painleve/Unique.lean).
Statement approved by independent check (GPT-6 Pro, job_abc1a83b). Acceptance:
`example : Stmt_unique := unique_theorem` compiles; axioms propext,
Classical.choice, Quot.sound only; no sorry in 38 modules (8458 lines).
Proof: UniqBounds (integrated form, bounds, logarithmic mean), Energy
(power-weighted localized energy estimate), Unique (assembly), following
paper Section 7.

## Historical planning notes (superseded)

The notes below were written during the formalization. Both routes were
adopted and the paper now presents them (Lemma 4.3 and Lemma 5.1); they are
kept as a record only.

### Route for Lemmas 3.1 and 4.3 in Lean (one-variable calculus only)

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

### Route notes (Lean vs paper)

- Lemma 4.3 (planning item 6): superseded by the exponential-coordinate route above.
- Lemma 5.1 (planning item 8): the paper then cited the Dixon–Ferrar formula (G&R 6.518). Lean plan:
  both `hBessel` and `C Φ_{0,0}(1; a²/2)` solve `h''' + a² h' + a h = 0`, and
  their values of h, h′, h″ as a → 0⁺ are `C·B(1/4,1/4)/2`, `−π`,
  `C·B(3/4,3/4)` (checked numerically to ~10 digits, 2026-10-23); linear ODE
  uniqueness gives equality. Mirror into the paper if adopted.

### Reuse survey (Yang–Mills Lean, 2026-10-23)

No importable infrastructure for this project (fractional Bessel, Andréief,
indefinite orthogonal polynomials, ℂ integration by parts, Beta integrals are
absent). Patterns worth copying: `HermiteScale.lean`
(`paperPolynomialGaussianIntegrable`, Gaussian integration by parts),
`CB182L.lean` (Cauchy product of Bessel-type series),
`FAM088Core3.lean` (polar-coordinate wrappers).
