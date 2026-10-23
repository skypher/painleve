import Painleve.Statement
import Painleve.Signs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic

/-!
# The quartic recurrence from the Hermitian form (Section 6 of `paper.tex`)

We work with an abstract form `B` on `ℂ[X]` that is linear in the first
argument, Hermitian, orthogonal across `C₄`-weights, and satisfies the
integration by parts `(L f, z^q) = -τ(q) a (f, z^{q+1})` with
`L = ∂_z + i z³` (`eq:ibp-pairing`). Given monic orthogonal polynomials with
signed norms `ϱ(n) 𝔥_n`, `𝔥_n > 0`, the ratios `v_n = 𝔥_{n+1}/(a 𝔥_n)` solve
`eq:quartic-recurrence`.
-/

open Polynomial Finset
open scoped ComplexConjugate

namespace Painleve

/-- Hypotheses on the form, Section 6. -/
structure FormHyp (B : ℂ[X] → ℂ[X] → ℂ) (a : ℝ) : Prop where
  add_left : ∀ f g k, B (f + g) k = B f k + B g k
  smul_left : ∀ (c : ℂ) f k, B (C c * f) k = c * B f k
  herm : ∀ f g, B f g = conj (B g f)
  weight : ∀ p q : ℕ, p % 4 ≠ q % 4 → B (X ^ p) (X ^ q) = 0
  ibp : ∀ (f : ℂ[X]) (q : ℕ),
    B (derivative f + C Complex.I * X ^ 3 * f) (X ^ q) = -(tau q : ℂ) * a * B f (X ^ (q + 1))

/-- Monic orthogonal polynomials with positive signed norms. -/
structure OPData (B : ℂ[X] → ℂ[X] → ℂ) where
  P : ℕ → ℂ[X]
  h : ℕ → ℝ
  monic : ∀ n, (P n).Monic
  deg : ∀ n, (P n).natDegree = n
  orth : ∀ n, ∀ j < n, B (P n) (X ^ j) = 0
  norm : ∀ n, B (P n) (P n) = ((rhoSign n * h n : ℝ) : ℂ)
  pos : ∀ n, 0 < h n

variable {B : ℂ[X] → ℂ[X] → ℂ} {a : ℝ}

namespace FormHyp

variable (hB : FormHyp B a)
include hB

theorem zero_left (k : ℂ[X]) : B 0 k = 0 := by
  have := hB.add_left 0 0 k
  simp only [add_zero] at this
  linear_combination -this

theorem neg_left (f k : ℂ[X]) : B (-f) k = -B f k := by
  have := hB.smul_left (-1) f k
  simpa using this

theorem sub_left (f g k : ℂ[X]) : B (f - g) k = B f k - B g k := by
  rw [sub_eq_add_neg, hB.add_left, hB.neg_left, ← sub_eq_add_neg]

theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (k : ℂ[X]) :
    B (∑ i ∈ s, f i) k = ∑ i ∈ s, B (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB.zero_left]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, hB.add_left, ih]

theorem add_right (f g k : ℂ[X]) : B k (f + g) = B k f + B k g := by
  rw [hB.herm, hB.add_left, map_add, ← hB.herm, ← hB.herm]

theorem smul_right (c : ℂ) (f k : ℂ[X]) : B k (C c * f) = conj c * B k f := by
  rw [hB.herm, hB.smul_left, map_mul, ← hB.herm]

theorem zero_right (k : ℂ[X]) : B k 0 = 0 := by
  rw [hB.herm, hB.zero_left, map_zero]

theorem sub_right (f g k : ℂ[X]) : B k (f - g) = B k f - B k g := by
  rw [hB.herm, hB.sub_left, map_sub, ← hB.herm, ← hB.herm]

theorem sum_right {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (k : ℂ[X]) :
    B k (∑ i ∈ s, f i) = ∑ i ∈ s, B k (f i) := by
  rw [hB.herm, hB.sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hB.herm _ _).symm

theorem expand_left (f k : ℂ[X]) (N : ℕ) (hN : f.natDegree < N) :
    B f k = ∑ i ∈ range N, f.coeff i * B (X ^ i) k := by
  conv_lhs => rw [as_sum_range' f N hN]
  rw [hB.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← C_mul_X_pow_eq_monomial, hB.smul_left]

theorem expand_right (f k : ℂ[X]) (N : ℕ) (hN : f.natDegree < N) :
    B k f = ∑ i ∈ range N, conj (f.coeff i) * B k (X ^ i) := by
  conv_lhs => rw [as_sum_range' f N hN]
  rw [hB.sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← C_mul_X_pow_eq_monomial, hB.smul_right]

end FormHyp


/-- `f` has `C₄`-weight `r`: its coefficients vanish off the residue class of `r`. -/
def IsWt (f : ℂ[X]) (r : ℕ) : Prop := ∀ i, i % 4 ≠ r % 4 → f.coeff i = 0

/-- The operator `L = ∂_z + i z³`. -/
noncomputable def Lop (f : ℂ[X]) : ℂ[X] := derivative f + C Complex.I * X ^ 3 * f

theorem isWt_X_mul {f : ℂ[X]} {r : ℕ} (hf : IsWt f r) : IsWt (X * f) (r + 1) := by
  intro i hi
  rcases i with _ | i
  · exact coeff_X_mul_zero f
  · rw [coeff_X_mul]
    exact hf i (by omega)

theorem isWt_Lop {f : ℂ[X]} {r : ℕ} (hf : IsWt f r) : IsWt (Lop f) (r + 3) := by
  intro i hi
  rw [Lop, coeff_add, coeff_derivative, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  rw [hf (i + 1) (by omega), zero_mul, zero_add]
  split_ifs with h
  · rw [hf (i - 3) (by omega), mul_zero]
  · rw [mul_zero]

theorem natDegree_Lop_le (f : ℂ[X]) : (Lop f).natDegree ≤ f.natDegree + 3 := by
  unfold Lop
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_derivative_le f).trans (by omega)
  · rw [mul_assoc]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_mul_le.trans ?_
    have := natDegree_X_pow_le (R := ℂ) 3
    omega

theorem coeff_Lop_add_three (f : ℂ[X]) (n : ℕ) (hf : f.natDegree ≤ n) :
    (Lop f).coeff (n + 3) = Complex.I * f.coeff n := by
  rw [Lop, coeff_add, coeff_derivative, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < n + 3 + 1), zero_mul, zero_add,
    if_pos (by omega), show n + 3 - 3 = n by omega]

namespace FormHyp

variable (hB : FormHyp B a)
include hB

theorem wt_orth (f g : ℂ[X]) (r s : ℕ) (hf : IsWt f r) (hg : IsWt g s) (hrs : r % 4 ≠ s % 4) :
    B f g = 0 := by
  rw [hB.expand_left f g (f.natDegree + 1) (by omega)]
  refine sum_eq_zero fun i _ => ?_
  by_cases hi : i % 4 = r % 4
  · rw [hB.expand_right g (X ^ i) (g.natDegree + 1) (by omega), sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : j % 4 = s % 4
    · rw [hB.weight i j (by omega), mul_zero]
    · rw [hg j hj, map_zero, zero_mul]
  · rw [hf i hi, zero_mul]

theorem mul_X_right (f g : ℂ[X]) :
    B f (X * g) = ∑ j ∈ range (g.natDegree + 1), conj (g.coeff j) * B f (X ^ (j + 1)) := by
  rw [hB.expand_right (X * g) f (g.natDegree + 2), sum_range_succ', coeff_X_mul_zero, map_zero,
    zero_mul, add_zero]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_X_mul]
  · have h1 := natDegree_mul_le (p := (X : ℂ[X])) (q := g)
    have : (X : ℂ[X]).natDegree ≤ 1 := natDegree_X_le
    omega

/-- Integration by parts against a polynomial of a single weight. -/
theorem ibp_wt (f g : ℂ[X]) (r : ℕ) (hg : IsWt g r) :
    B (Lop f) g = -(tau r : ℂ) * a * B f (X * g) := by
  rw [hB.expand_right g (Lop f) (g.natDegree + 1) (by omega), hB.mul_X_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j % 4 = r % 4
  · have htau : tau j = tau r := by unfold tau; rw [hj]
    rw [Lop, hB.ibp, htau]
    ring
  · rw [hg j hj, map_zero, zero_mul, zero_mul, mul_zero]

end FormHyp

namespace OPData

variable (hB : FormHyp B a) (D : OPData B)
include hB

omit hB in
theorem rhoSign_ne_zero (n : ℕ) : rhoSign n ≠ 0 := by
  rw [rhoSign_eq]; exact pow_ne_zero _ (by norm_num)

omit hB in
theorem norm_ne_zero (n : ℕ) : B (D.P n) (D.P n) ≠ 0 := by
  rw [D.norm]
  exact_mod_cast mul_ne_zero (rhoSign_ne_zero n) (D.pos n).ne'

omit hB in
theorem coeff_self (n : ℕ) : (D.P n).coeff n = 1 := by
  have := D.monic n; rw [Monic, leadingCoeff, D.deg n] at this; exact this

theorem left_P (g : ℂ[X]) (n : ℕ) (hg : g.natDegree ≤ n) :
    B g (D.P n) = g.coeff n * B (X ^ n) (D.P n) := by
  rw [hB.expand_left g (D.P n) (n + 1) (by omega), sum_range_succ, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [hB.herm, D.orth n i (mem_range.mp hi), map_zero, mul_zero]

/-- Coefficient extraction against `P n`. -/
theorem extract (g : ℂ[X]) (n : ℕ) (hg : g.natDegree ≤ n) :
    B g (D.P n) = g.coeff n * B (D.P n) (D.P n) := by
  have h2 := left_P hB D (D.P n) n (D.deg n).le
  rw [coeff_self, one_mul] at h2
  rw [left_P hB D g n hg, h2]

theorem lower_left (g : ℂ[X]) (n : ℕ) (hg : g.natDegree < n) : B g (D.P n) = 0 := by
  rw [extract hB D g n hg.le, coeff_eq_zero_of_natDegree_lt hg, zero_mul]

theorem lower_right (g : ℂ[X]) (n : ℕ) (hg : g.natDegree < n) : B (D.P n) g = 0 := by
  rw [hB.herm, lower_left hB D g n hg, map_zero]

theorem P_P (m k : ℕ) : B (D.P m) (D.P k) = if m = k then B (D.P k) (D.P k) else 0 := by
  split_ifs with h
  · rw [h]
  · rcases lt_or_gt_of_ne h with hmk | hmk
    · exact lower_left hB D _ k (by rw [D.deg]; exact hmk)
    · exact lower_right hB D _ m (by rw [D.deg]; exact hmk)

/-- A polynomial of degree `≤ N` orthogonal to `P 0, …, P N` vanishes. -/
theorem vanish (g : ℂ[X]) (N : ℕ) (hg : g.natDegree ≤ N) (h0 : ∀ k ≤ N, B g (D.P k) = 0) :
    g = 0 := by
  by_contra hne
  have := extract hB D g g.natDegree le_rfl
  rw [h0 _ hg, coeff_natDegree] at this
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hne) (norm_ne_zero D _) this.symm

end OPData


/-- Projection of `f` onto the weight space of `r`. -/
noncomputable def wproj (f : ℂ[X]) (r : ℕ) : ℂ[X] :=
  ∑ i ∈ range (f.natDegree + 1), if i % 4 = r % 4 then C (f.coeff i) * X ^ i else 0

theorem coeff_wproj (f : ℂ[X]) (r j : ℕ) :
    (wproj f r).coeff j = if j % 4 = r % 4 then f.coeff j else 0 := by
  unfold wproj
  rw [finsetSum_coeff]
  simp_rw [apply_ite (fun p : ℂ[X] => p.coeff j), coeff_C_mul_X_pow, coeff_zero]
  by_cases hj : j < f.natDegree + 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro h; exact absurd (mem_range.mpr hj) h
  · rw [Finset.sum_eq_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
    · simp
    · intro i hi
      have : j ≠ i := by have := mem_range.mp hi; omega
      simp [this]

theorem natDegree_wproj_le (f : ℂ[X]) (r : ℕ) : (wproj f r).natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_wproj]
  split_ifs
  · exact coeff_eq_zero_of_natDegree_lt hN
  · rfl

theorem tau_ne_zero (l : ℕ) : (tau l : ℂ) ≠ 0 := by
  unfold tau; split_ifs <;> norm_num

theorem tau_mul_self' (l : ℕ) : (tau l : ℂ) * tau l = 1 := by
  unfold tau; split_ifs <;> norm_num

namespace FormHyp

variable (hB : FormHyp B a)
include hB

theorem wproj_X_pow (f : ℂ[X]) (r j : ℕ) :
    B (wproj f r) (X ^ j) = if j % 4 = r % 4 then B f (X ^ j) else 0 := by
  rw [hB.expand_left (wproj f r) _ (f.natDegree + 1)
    (lt_of_le_of_lt (natDegree_wproj_le f r) (by omega))]
  split_ifs with hj
  · rw [hB.expand_left f (X ^ j) (f.natDegree + 1) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_wproj]
    split_ifs with hi
    · rfl
    · rw [hB.weight i j (by omega), mul_zero, mul_zero]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_wproj]
    split_ifs with hi
    · rw [hB.weight i j (by omega), mul_zero]
    · rw [zero_mul]

end FormHyp

namespace OPData

variable (hB : FormHyp B a) (D : OPData B)
include hB

/-- `P n` lies in the weight space of `n`. -/
theorem P_isWt (n : ℕ) : IsWt (D.P n) n := by
  have hQ : wproj (D.P n) n = D.P n := by
    have hv := vanish hB D (wproj (D.P n) n - D.P n) n ?_ ?_
    · exact sub_eq_zero.mp hv
    · refine (natDegree_sub_le _ _).trans (max_le ?_ (D.deg n).le)
      exact (natDegree_wproj_le _ _).trans (D.deg n).le
    · intro k hk
      rw [hB.expand_right (D.P k) _ (k + 1) (by rw [D.deg]; omega)]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk := mem_range.mp hj
      rw [hB.sub_left, hB.wproj_X_pow]
      split_ifs with hjn
      · rw [sub_self, mul_zero]
      · rw [D.orth n j (by omega), sub_zero, mul_zero]
  intro i hi
  rw [← hQ, coeff_wproj, if_neg hi]

/-- Band structure of multiplication by `z`. -/
theorem band (ha : 0 < a) (n k : ℕ) (hk : k ≤ n) (hk3 : k + 3 ≠ n) :
    B (X * D.P n) (D.P k) = 0 := by
  by_cases hw : k % 4 = (n + 1) % 4
  · have hibp := hB.ibp_wt (D.P k) (D.P n) n (P_isWt hB D n)
    rw [lower_left hB D (Lop (D.P k)) n (by
      have := natDegree_Lop_le (D.P k); rw [D.deg] at this; omega)] at hibp
    have hne : (-(tau n : ℂ) * a) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (tau_ne_zero n)) (by exact_mod_cast ha.ne')
    have h0 : B (D.P k) (X * D.P n) = 0 := by
      rcases mul_eq_zero.mp hibp.symm with h | h
      · exact absurd h hne
      · exact h
    rw [hB.herm, h0, map_zero]
  · exact hB.wt_orth _ _ (n + 1) k (isWt_X_mul (P_isWt hB D n)) (P_isWt hB D k) (by omega)

end OPData


namespace OPData

/-- The lower coefficient `c_n = (i/a) 𝔥_n / 𝔥_{n-3}` in `z P_n = P_{n+1} + c_n P_{n-3}`. -/
noncomputable def cc (D : OPData B) (a : ℝ) (n : ℕ) : ℂ :=
  if 3 ≤ n then Complex.I / a * ((D.h n / D.h (n - 3) : ℝ) : ℂ) else 0

variable (hB : FormHyp B a) (D : OPData B)
include hB

theorem cformula (ha : 0 < a) (n : ℕ) (hn : 3 ≤ n) :
    B (X * D.P n) (D.P (n - 3)) = D.cc a n * B (D.P (n - 3)) (D.P (n - 3)) := by
  have hibp := hB.ibp_wt (D.P (n - 3)) (D.P n) n (P_isWt hB D n)
  have hL : B (Lop (D.P (n - 3))) (D.P n) = Complex.I * B (D.P n) (D.P n) := by
    rw [extract hB D _ n (by
      have := natDegree_Lop_le (D.P (n - 3)); rw [D.deg] at this; omega)]
    congr 1
    have := coeff_Lop_add_three (D.P (n - 3)) (n - 3) (D.deg _).le
    rw [show n - 3 + 3 = n by omega, coeff_self, mul_one] at this
    exact this
  rw [hL] at hibp
  -- hibp : I N_n = -(τ n) a β with β = B (P (n-3)) (X P n)
  have hτ := tau_mul_self' n
  have hρ : rhoSign n = tau n * rhoSign (n - 3) := by
    have := rhoSign_add_three (n - 3); rwa [show n - 3 + 3 = n by omega] at this
  have hh3 : (D.h (n - 3) : ℂ) ≠ 0 := by exact_mod_cast (D.pos (n - 3)).ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hβ : B (D.P (n - 3)) (X * D.P n) =
      -(Complex.I * ((rhoSign n * D.h n : ℝ) : ℂ)) * (tau n : ℂ) / a := by
    rw [D.norm] at hibp
    field_simp
    linear_combination (tau n : ℂ) * hibp - B (D.P (n - 3)) (X * D.P n) * a * hτ
  rw [hB.herm, hβ, D.norm, cc, if_pos hn]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [hρ]
  push_cast
  field_simp
  linear_combination ((rhoSign (n - 3) : ℂ) * (D.h n : ℂ)) * hτ

/-- The two-term relation `z P_n = P_{n+1} + c_n P_{n-3}` (`eq:polynomial-recurrences`). -/
theorem two_term (ha : 0 < a) (n : ℕ) :
    X * D.P n = D.P (n + 1) + C (D.cc a n) * D.P (n - 3) := by
  have hv := vanish hB D (X * D.P n - D.P (n + 1) - C (D.cc a n) * D.P (n - 3)) n ?_ ?_
  · linear_combination hv
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, coeff_sub, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (by rw [D.deg]; omega : (D.P (n - 3)).natDegree < N),
      mul_zero, sub_zero]
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [coeff_X_mul]
    rcases Nat.lt_or_ge n M with hM | hM
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [D.deg]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [D.deg]; omega), sub_zero]
    · have : M = n := by omega
      subst this
      rw [coeff_self, coeff_self, sub_self]
  · intro k hk
    rw [hB.sub_left, hB.sub_left, hB.smul_left, P_P hB D (n + 1) k, if_neg (by omega), sub_zero]
    by_cases hk3 : k + 3 = n
    · have hn3 : n - 3 = k := by omega
      rw [← hn3, cformula hB D ha n (by omega), P_P hB D, if_pos rfl, sub_self]
    · rw [band hB D ha n k hk hk3, zero_sub, neg_eq_zero, P_P hB D]
      by_cases h3 : 3 ≤ n
      · rw [if_neg (by omega), mul_zero]
      · rw [cc, if_neg h3, zero_mul]

/-- Pairing `z P_k` with `P_m`. -/
theorem mulX_pair (ha : 0 < a) (k m : ℕ) :
    B (X * D.P k) (D.P m) =
      (if k + 1 = m then B (D.P m) (D.P m) else 0) +
        (if 3 ≤ k ∧ k - 3 = m then D.cc a k * B (D.P m) (D.P m) else 0) := by
  rw [two_term hB D ha k, hB.add_left, hB.smul_left, P_P hB D (k + 1) m, P_P hB D (k - 3) m]
  congr 1
  by_cases h3 : 3 ≤ k <;> by_cases hm : k - 3 = m <;> simp [cc, h3, hm]

end OPData


namespace OPData

variable (hB : FormHyp B a) (D : OPData B)
include hB

/-- The coefficient of `P_{n-1}` in `z³ P_n` is `c_n + c_{n+1} + c_{n+2}`. -/
theorem X3_pair (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    B (X ^ 3 * D.P n) (D.P (n - 1)) =
      (D.cc a n + D.cc a (n + 1) + D.cc a (n + 2)) * B (D.P (n - 1)) (D.P (n - 1)) := by
  have e0 : X * D.P n = D.P (n + 1) + C (D.cc a n) * D.P (n - 3) := two_term hB D ha n
  have e1 : X * D.P (n + 1) = D.P (n + 2) + C (D.cc a (n + 1)) * D.P (n + 1 - 3) :=
    two_term hB D ha (n + 1)
  have e2 : X * D.P (n - 3) = D.P (n - 3 + 1) + C (D.cc a (n - 3)) * D.P (n - 3 - 3) :=
    two_term hB D ha (n - 3)
  have hX3 : X ^ 3 * D.P n = X * D.P (n + 2) + C (D.cc a (n + 1)) * (X * D.P (n + 1 - 3))
      + C (D.cc a n) * (X * D.P (n - 3 + 1))
      + C (D.cc a n * D.cc a (n - 3)) * (X * D.P (n - 3 - 3)) := by
    calc X ^ 3 * D.P n = X * (X * (X * D.P n)) := by ring
      _ = X * (X * D.P (n + 1)) + C (D.cc a n) * (X * (X * D.P (n - 3))) := by rw [e0]; ring
      _ = _ := by rw [e1, e2, C_mul]; ring
  rw [hX3, hB.add_left, hB.add_left, hB.add_left, hB.smul_left, hB.smul_left, hB.smul_left,
    mulX_pair hB D ha, mulX_pair hB D ha, mulX_pair hB D ha, mulX_pair hB D ha]
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n) with
    rfl | rfl | rfl | rfl | rfl | h6
  · simp [cc]
  · simp [cc]; ring
  · simp [cc]; ring
  · simp [cc]; ring
  · simp [cc]; ring
  · rw [if_neg (show ¬ (n + 2 + 1 = n - 1) by omega),
      if_pos (show 3 ≤ n + 2 ∧ n + 2 - 3 = n - 1 by omega),
      if_pos (show n + 1 - 3 + 1 = n - 1 by omega),
      if_neg (show ¬ (3 ≤ n + 1 - 3 ∧ n + 1 - 3 - 3 = n - 1) by omega),
      if_pos (show n - 3 + 1 + 1 = n - 1 by omega),
      if_neg (show ¬ (3 ≤ n - 3 + 1 ∧ n - 3 + 1 - 3 = n - 1) by omega),
      if_neg (show ¬ (n - 3 - 3 + 1 = n - 1) by omega),
      if_neg (show ¬ (3 ≤ n - 3 - 3 ∧ n - 3 - 3 - 3 = n - 1) by omega)]
    ring

/-- The complex form of the recurrence (`eq:V-recurrence` before normalization). -/
theorem rec_complex (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) * B (D.P (n - 1)) (D.P (n - 1)) +
        Complex.I * ((D.cc a n + D.cc a (n + 1) + D.cc a (n + 2)) * B (D.P (n - 1)) (D.P (n - 1))) =
      -(tau (n - 1) : ℂ) * a * B (D.P n) (D.P n) := by
  have hibp := hB.ibp_wt (D.P n) (D.P (n - 1)) (n - 1) (P_isWt hB D (n - 1))
  have hX : X * D.P (n - 1) = D.P n + C (D.cc a (n - 1)) * D.P (n - 1 - 3) := by
    have := two_term hB D ha (n - 1); rwa [show n - 1 + 1 = n by omega] at this
  rw [hX, hB.add_right, hB.smul_right, P_P hB D n (n - 1 - 3), if_neg (by omega), mul_zero,
    add_zero] at hibp
  rw [← hibp, Lop, hB.add_left, mul_assoc, hB.smul_left, X3_pair hB D ha n hn,
    extract hB D (derivative (D.P n)) (n - 1)
      ((natDegree_derivative_le _).trans (by rw [D.deg]))]
  congr 1
  rw [coeff_derivative, show n - 1 + 1 = n by omega, coeff_self, one_mul]
  push_cast [Nat.cast_sub hn]
  ring

end OPData


namespace OPData

variable (hB : FormHyp B a) (D : OPData B)
include hB

/-- The real recurrence on the signed norms, solved for `𝔥_{m+3}`. -/
theorem rec_real (ha : 0 < a) (m : ℕ) :
    D.h (m + 3) = a * ((m : ℝ) + 1) * D.h m - a ^ 2 * D.h (m + 1)
      - ((if 3 ≤ m + 1 then D.h (m + 1) / D.h (m + 1 - 3) else 0)
        + (if 3 ≤ m + 2 then D.h (m + 2) / D.h (m + 2 - 3) else 0)) * D.h m := by
  have hc := rec_complex hB D ha (m + 1) (by omega)
  simp only [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega,
    show m + 1 + 2 = m + 3 by omega] at hc
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hII : ∀ k : ℕ, Complex.I * D.cc a k =
      -(((if 3 ≤ k then D.h k / D.h (k - 3) else 0 : ℝ) : ℂ) / a) := by
    intro k
    unfold cc
    split_ifs
    · push_cast
      field_simp
      rw [Complex.I_sq]
      ring
    · simp
  have hsum : Complex.I * ((D.cc a (m + 1) + D.cc a (m + 2) + D.cc a (m + 3)) *
      B (D.P m) (D.P m)) = (Complex.I * D.cc a (m + 1) + Complex.I * D.cc a (m + 2) +
        Complex.I * D.cc a (m + 3)) * B (D.P m) (D.P m) := by ring
  rw [hsum, hII, hII, hII, if_pos (by omega : 3 ≤ m + 3), show m + 3 - 3 = m by omega,
    D.norm, D.norm, rhoSign_succ m] at hc
  have hτ : (tau m : ℂ) * tau m = 1 := by exact_mod_cast tau_mul_self m
  have hρ0 : (rhoSign m : ℂ) ≠ 0 := by exact_mod_cast rhoSign_ne_zero m
  have hm0 : (D.h m : ℂ) ≠ 0 := by exact_mod_cast (D.pos m).ne'
  set A1 : ℝ := if 3 ≤ m + 1 then D.h (m + 1) / D.h (m + 1 - 3) else 0 with hA1
  set A2 : ℝ := if 3 ≤ m + 2 then D.h (m + 2) / D.h (m + 2 - 3) else 0 with hA2
  -- clear the denominators `a` and `𝔥_m`
  have key : (rhoSign m : ℂ) * ((D.h (m + 3) : ℂ) - (a * ((m : ℂ) + 1) * D.h m - a ^ 2 * D.h (m + 1)
      - ((A1 : ℂ) + A2) * D.h m)) = 0 := by
    push_cast at hc
    field_simp at hc
    linear_combination (-(rhoSign m : ℂ)) * hc - (rhoSign m : ℂ) * (a : ℂ) ^ 2 * (D.h (m + 1) : ℂ) * hτ
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hρ0
  · have := sub_eq_zero.mp h
    exact_mod_cast this

/-- **Section 6.** The ratios `v_n = 𝔥_{n+1} / (a 𝔥_n)` solve the quartic recurrence. -/
theorem quarticRec (ha : 0 < a) : QuarticRec a (fun n => D.h (n + 1) / (a * D.h n)) := by
  intro m
  have hr := rec_real hB D ha m
  have ha' : a ≠ 0 := ha.ne'
  have h0 : ∀ k, D.h k ≠ 0 := fun k => (D.pos k).ne'
  have hm3 : D.h (m + 2 + 1) = D.h (m + 3) := rfl
  rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | hm
  · simp only [extZ, show ((0 : ℕ) : ℤ) - 1 < 0 by omega, show ((0 : ℕ) : ℤ) - 2 < 0 by omega,
      if_true]
    norm_num at hr ⊢
    rw [hr]
    have := h0 0; have := h0 1; have := h0 2
    field_simp
    ring
  · simp only [extZ, show ¬ (((1 : ℕ) : ℤ) - 1 < 0) by omega,
      show ((1 : ℕ) : ℤ) - 2 < 0 by omega, if_true, if_false]
    norm_num at hr ⊢
    rw [hr]
    have := h0 0; have := h0 1; have := h0 2; have := h0 3
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    have e1 : extZ (fun n => D.h (n + 1) / (a * D.h n)) (((j + 2 : ℕ) : ℤ) - 1) =
        D.h (j + 2) / (a * D.h (j + 1)) := by
      simp only [extZ, show ¬ (((j + 2 : ℕ) : ℤ) - 1 < 0) by omega, if_false]
      rw [show (((j + 2 : ℕ) : ℤ) - 1).toNat = j + 1 by omega]
    have e2 : extZ (fun n => D.h (n + 1) / (a * D.h n)) (((j + 2 : ℕ) : ℤ) - 2) =
        D.h (j + 1) / (a * D.h j) := by
      simp only [extZ, show ¬ (((j + 2 : ℕ) : ℤ) - 2 < 0) by omega, if_false]
      rw [show (((j + 2 : ℕ) : ℤ) - 2).toNat = j by omega]
    rw [e1, e2]
    rw [if_pos (by omega), if_pos (by omega), show j + 2 + 1 - 3 = j by omega,
      show j + 2 + 2 - 3 = j + 1 by omega] at hr
    simp only [show j + 2 + 1 + 1 = j + 4 by omega, show j + 2 + 2 = j + 4 by omega,
      show j + 2 + 1 = j + 3 by omega, show j + 2 + 3 = j + 5 by omega,
      show j + 4 + 1 = j + 5 by omega] at hr ⊢
    rw [hr]
    have := h0 j; have := h0 (j + 1); have := h0 (j + 2); have := h0 (j + 3); have := h0 (j + 4)
    push_cast
    field_simp
    ring

end OPData

end Painleve
