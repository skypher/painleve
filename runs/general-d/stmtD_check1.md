## Verdicts

| Statement | Verdict |
|---|---|
| `Painleve.Stmt_mainD` | **APPROVE** |
| `Painleve.Stmt_uniqueD` | **REJECT as a standalone encoding of the complete theorem** |
| `Painleve.Stmt_endpoint` | **APPROVE** |

The two failures are missing **existence assertions in the “In particular” consequences** of `Stmt_uniqueD`. Its asymptotic assertion and at-most-one assertion are correct. Its consequences are adequate **when combined with the earlier existence theorems**, but alone are weaker than saying that the specified sequences *are the unique positive solutions*.

This is a semantic statement audit, not a compilation certificate. Mathlib conventions were checked against the cited commit `db584cd6d46c`. Paper references below refer to the supplied text.

## Shared definitions and `Stmt_mainD`

| Knob | Result | Finding |
|---|---|---|
| Quantifiers and parameter ranges | **PASS** | `∀ d ≥ 2, ∀ a > 0`; part (ii) is guarded by `3 ≤ d`. All sequence and polynomial degrees range over every natural number, including zero. |
| Density | **PASS** | Exactly `eq:density`: complex exponential, coefficient `i/d`, and Gaussian factor `−a‖z‖²`. |
| Area measure | **PASS** | The implicit measure is complex `volume`, equal to ordinary planar Lebesgue measure—not probability-normalized area. [1] |
| `etaD` | **PASS** | Exactly `exp(πi/d)`. Division is complex division after coercion, not natural-number division. |
| Twist and `χ(r)=r` | **PASS** | The residue is `m % d`, converted to `ℤ` **before negation**. For `m=r+dq`, the multiplier is `(-η)⁻ʳηᵐ=(-1)^(r+q)`, matching `eq:twist-sign`. |
| Pairing convention | **PASS** | Linear in `f`, conjugate-linear in `g`; conjugation surrounds the evaluation of the entire twisted polynomial. |
| Gram matrices and block convention | **PASS** | `gramLeadD … n` is the matrix of size `n`, indexed by degrees `0,…,n−1`. Restriction to residue `r` gives `Gᵣ[p,q]=(-1)^(r+q) Mᵣ[p,q]`, with the sign on the column index as required. |
| `tauD` | **PASS** | Correct boundary sign `(-1)^(d−1)`. Its domain is only `ℕ`, whereas the paper also defines negative arguments; this loses no content here because every use is at a nonnegative index. |
| `rhoSignD` | **PASS** | The product includes exactly `ℓ=0,…,n−1`. For `n=r+dq`, the sign simplifies to `(-1)^(r+q)`, for both odd and even `d`. |
| Signed norms | **PASS** | Nondegeneracy makes the determinant quotient legitimate. Hermitian symmetry makes it real, so `.re` discards nothing. Multiplication by `rhoSignD` agrees with the paper because this sign squares to one. |
| Monic orthogonal polynomials | **PASS** | Exact degree, existence, uniqueness, and orthogonality against every lower monomial are encoded. `Monic` excludes the zero polynomial, including when `n=0`. |
| Norm identification | **PASS** | The explicit equality `(P,P)=ϱ(n)𝔥ₙ` identifies the determinant-defined quantity with the paper’s signed norm. These polynomial clauses are consequences of the intended nondegenerate Gram formulation, not substantive strengthenings. |
| `FHRec` ranges | **PASS** | Both ranges contain `0,…,d−2`, hence `d−1` summands and `d−1` factors per product. The coefficient and right-hand side are exactly `a⁻²` and `(n+1)/a`. |
| Negative indices and subtraction | **PASS** | Arithmetic in `(n : ℤ) + j - k` is integer arithmetic. `extZ` returns zero before using `toNat` on negative arguments; there is no natural-subtraction truncation. |
| Initial values | **PASS** | `j < d−2` is exactly `0≤j≤d−3`. Equality is in `ℂ`, so the definition requires the entire moment quotient—not merely its real part—to equal the real sequence value. |
| Required nonzero moments | **PASS** | Denominators `M₀,…,M_{d−3}` are explicitly nonzero. Existence and positivity of the solution also force the numerators `M₁,…,M_{d−2}` to be nonzero. There is no missing denominator condition. |
| Real-sequence uniqueness | **PASS** | `∃! V, IsSolD … V` quantifies over **all real sequences**, without assuming positivity. Positivity and identification with the norm ratios are then asserted for every solution. |

The additional size-zero Gram assertion is harmless: its determinant is `1`.

## `Stmt_uniqueD`

| Knob | Result | Finding |
|---|---|---|
| Quantifier order | **PASS** | Arbitrary `d≥3` and `ε>0` precede the sequences. There is no initial-data restriction. |
| `GenRec` | **PASS** | The starting index is `m=n−j`, with `j=0,…,d−2`; its factors are `v_m,…,v_{m+d−2}`. This is exactly `eq:general-recurrence`. |
| Normalization | **PASS** | Reindexing the FH windows and substituting `V=a^(2/(d−2))v` gives this recurrence with `ε=a^(−d/(d−2))`. All powers here have positive base `a`. |
| Asymptotics | **PASS** | The limit uses every `n→∞`, the exact factor `(d−1)/(ε(n+1))`, real exponent `1/(d−1)`, and limit `1`. |
| At-most-one positive solution | **PASS** | Any two everywhere-positive solutions are equal as functions. Nonexistence is permissible for this clause because the paper explicitly says “at most one.” |
| **U1: FH “unique positive solution” consequence** | **FAIL — weaker** | The code only says that **any existing** positive FH solution equals the norm-ratio sequence. It does not assert that the norm-ratio sequence is positive or satisfies `FHRec`. |
| **U2: Quartic “unique positive solution” consequence** | **FAIL — weaker** | The code only says that **any existing** positive quartic solution satisfies `IsSolution`. It does not supply a positive quartic solution. Uniqueness follows from the first conjunct, but existence is missing. |

Thus neither consequence, considered without the earlier existence results, rules out an empty positive-solution class. The supplied “demand sheet” describes the weaker conditional clauses accurately, but those comments do not restore the omitted existence assertions.

## Endpoint statement

| Knob | Result | Finding |
|---|---|---|
| Quantifiers | **PASS** | Every `d≥2` and every natural `r<d`, exactly the paper’s range. |
| `J_r` | **PASS** | `range d` with `j ≠ d−1−r` removes precisely the specified index. Since `r<d`, the natural subtraction is exact here. |
| `j_r` | **PASS** | `jMin=1` precisely when `r=d−1`, otherwise `0`. This is `min J_r`, including `d=2`. |
| Shapes and `β_r` | **PASS** | `shapeD=(r+1+j)/d` uses real division, and the minimum shape is evaluated at `jMin`. |
| Product and prefactor | **PASS** | The filter removes both the absent index and `j_r`, giving exactly `J_r \ {j_r}`. The factorial, power of `d`, and Gamma quotients match the displayed corollary. Empty products correctly equal `1`. |
| Endpoint limit | **PASS** | `((a:ℂ)^jMin)⁻¹` equals the required `a^(−j_r)` for positive `a`. `𝓝[>] 0` is the right-sided limit, not evaluation at zero. |
| Positive finite constant | **PASS** | Positivity is explicit. Every retained Gamma argument and shape is positive, so there are no Gamma poles or zero denominators. Mathlib’s Gamma agrees with Euler’s integral on this domain. [2] |
| Matrix convergence | **PASS** | Matrix topology is the product topology, so `Tendsto` expresses entrywise convergence. [3] |
| Sizes below `d` | **PASS** | `n<d` means sizes through `d−1`, corresponding to the paper’s orders `N≤d−2`. Diagonality and nonzero determinant are both explicit. Size zero is a trivial addition. |
| Size `d` | **PASS** | Diagonality and **exact** rank `d−1` are explicit. `Matrix.rank` is natural-valued dimension of the image; finite matrices over `ℂ` have no infinite-dimension fallback issue. [4] |

The limit claims concern limits of the matrices for `a>0`; they correctly make **no claim about the totalized integral at `a=0`**.

## Junk-value audit

| Knob | Result | Finding |
|---|---|---|
| Division in `Stmt_mainD` | **PASS** | `d`, `a`, relevant Gram determinants, signed-norm denominators, and initial moment denominators are nonzero on the asserted domain. |
| Real powers | **PASS** | The asymptotic base and endpoint base are strictly positive. None uses Mathlib’s nonstandard extension of real powers to negative bases. [5] |
| Totalized integrals | **PASS** | Although Mathlib returns zero for nonintegrable functions, the relevant integrands for `a>0` are bounded in norm by polynomial growth times `exp(−a‖z‖²)`, hence integrable. Values outside that domain do not affect the right-sided endpoint limit. [6] |
| Bessel series and derivatives | **PASS on `a>0`** | The argument `a²/4` is positive; the series at orders `±1/4` converge and define smooth functions locally. No divergent-series or nondifferentiability default is being used there. See supplied `lem:bessel`. |
| `Classical.choose`, `sSup`, `sInf` | **PASS** | None is used in the supplied definitions to manufacture a solution, constant, or limit. |
| Vacuity | **FAIL only U1/U2** | Main existence is explicit, and the endpoint filter is nontrivial. The two uniqueness consequences omit witnesses, as identified above. |

## Specialization to `d=4`

**PASS, with the paper’s required rescaling.**

After simplification, the shared definitions agree:
`densityD 4`, `etaD 4`, `twistD 4`, `pairingD 4`, `gramLeadD 4`, `tauD 4`, `rhoSignD 4`, and `signedNormD 4` equal their counterparts in `Statement.lean`.

For the recurrence and solution predicates, the correct correspondences are

\[
\begin{aligned}
\operatorname{GenRec}(4,a^{-2},v)
&\iff \operatorname{QuarticRec}(a,v),\\
\operatorname{FHRec}(4,a,av)
&\iff \operatorname{QuarticRec}(a,v)\qquad(a>0),\\
\operatorname{IsSolD}(4,a,av)
&\iff \operatorname{IsSolution}(a,v)\qquad(a>0).
\end{aligned}
\]

The last equivalence uses the supplied Bessel identities
\[
M_0=h,\qquad M_1=-h',\qquad M_2=h''.
\]
Consequently `V_j=M_{j+1}/M_j` gives exactly the stated Bessel data for `v=V/a`, and the norm ratio becomes `𝔥_{n+1}/(a𝔥_n)`.

`FHRec 4 a v` is **not** directly the same predicate as `QuarticRec a v`; omitting this rescaling would be an error.

## Corrected Lean text for U1 and U2

Replace `Stmt_uniqueD` with the following. The first conjunct is unchanged; the other two now assert existence as well as uniqueness and identification.

```lean
def Stmt_uniqueD : Prop :=
  (∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, 0 < ε →
    (∀ v : ℕ → ℝ, (∀ n, 0 < v n) → GenRec d ε v →
      Tendsto (fun n : ℕ =>
          v n *
            (((d : ℝ) - 1) / (ε * ((n : ℝ) + 1))) ^
              (1 / ((d : ℝ) - 1)))
        atTop (𝓝 1)) ∧
    ∀ v w : ℕ → ℝ,
      (∀ n, 0 < v n) → (∀ n, 0 < w n) →
      GenRec d ε v → GenRec d ε w → v = w) ∧
  (∀ d : ℕ, 3 ≤ d → ∀ a : ℝ, 0 < a →
    let V : ℕ → ℝ := fun n =>
      signedNormD d a (n + 1) / signedNormD d a n
    (∀ n : ℕ, 0 < V n) ∧
      FHRec d a V ∧
      ∀ W : ℕ → ℝ, (∀ n, 0 < W n) →
        FHRec d a W → W = V) ∧
  (∀ a : ℝ, 0 < a →
    ∃ v : ℕ → ℝ,
      IsSolution a v ∧
      (∀ n : ℕ, 0 < v n) ∧
      ∀ w : ℕ → ℝ, (∀ n, 0 < w n) →
        QuarticRec a w → w = v)
```

The new positivity assertion for the norm-ratio sequence rules out zero norm denominators. The positive `IsSolution` witness likewise rules out zero Bessel denominators: either `hBessel a = 0` or `deriv hBessel a = 0` would force `v0 a = 0`.

**No changes are required to `Stmt_mainD`, `Stmt_endpoint`, or the shared mathematical definitions.**

Sources:
[1] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean
[2] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean
[3] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/Topology/Instances/Matrix.lean
[4] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/LinearAlgebra/Matrix/Rank.lean
[5] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
[6] https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean

