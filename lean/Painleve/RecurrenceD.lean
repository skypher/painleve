import Painleve.StatementD
import Painleve.AssemblyD
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic

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

open Polynomial Finset
open scoped ComplexConjugate

namespace Painleve

/-- Hypotheses on the form, Section 6. -/
structure FormHypD (d : ℕ) (B : ℂ[X] → ℂ[X] → ℂ) (a : ℝ) : Prop where
  add_left : ∀ f g k, B (f + g) k = B f k + B g k
  smul_left : ∀ (c : ℂ) f k, B (C c * f) k = c * B f k
  herm : ∀ f g, B f g = conj (B g f)
  weight : ∀ p q : ℕ, p % d ≠ q % d → B (X ^ p) (X ^ q) = 0
  ibp : ∀ (f : ℂ[X]) (q : ℕ),
    B (derivative f + C Complex.I * X ^ (d - 1) * f) (X ^ q) = -(tauD d q : ℂ) * a * B f (X ^ (q + 1))

/-- Monic orthogonal polynomials with positive signed norms. -/
structure OPDataD (d : ℕ) (B : ℂ[X] → ℂ[X] → ℂ) where
  P : ℕ → ℂ[X]
  h : ℕ → ℝ
  monic : ∀ n, (P n).Monic
  deg : ∀ n, (P n).natDegree = n
  orth : ∀ n, ∀ j < n, B (P n) (X ^ j) = 0
  norm : ∀ n, B (P n) (P n) = ((rhoSignD d n * h n : ℝ) : ℂ)
  pos : ∀ n, 0 < h n

variable {d : ℕ} {B : ℂ[X] → ℂ[X] → ℂ} {a : ℝ}

namespace FormHypD

variable (hB : FormHypD d B a)
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

end FormHypD

/-- `f` has weight `r` modulo `d`. -/
def IsWtD (d : ℕ) (f : ℂ[X]) (r : ℕ) : Prop := ∀ i, i % d ≠ r % d → f.coeff i = 0

/-- The operator `L = ∂_z + i z^{d-1}`. -/
noncomputable def LopD (d : ℕ) (f : ℂ[X]) : ℂ[X] := derivative f + C Complex.I * X ^ (d - 1) * f

lemma mod_succ_ne {i r : ℕ} (h : (i + 1) % d ≠ (r + 1) % d) : i % d ≠ r % d := by
  intro h'; apply h; rw [Nat.add_mod, h', ← Nat.add_mod]

theorem isWtD_X_mul {f : ℂ[X]} {r : ℕ} (hf : IsWtD d f r) : IsWtD d (X * f) (r + 1) := by
  intro i hi
  rcases i with _ | i
  · exact coeff_X_mul_zero f
  · rw [coeff_X_mul]
    exact hf i (mod_succ_ne hi)

lemma mod_add_ne {i r m : ℕ} (h : (i + m) % d ≠ (r + m) % d) : i % d ≠ r % d := by
  intro h'; apply h; rw [Nat.add_mod, h', ← Nat.add_mod]

theorem isWtD_Lop (hd : 0 < d) {f : ℂ[X]} {r : ℕ} (hf : IsWtD d f r) :
    IsWtD d (LopD d f) (r + (d - 1)) := by
  intro i hi
  rw [LopD, coeff_add, coeff_derivative, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  have h1 : (i + 1) % d ≠ r % d := by
    intro h'; apply hi
    have e : r + (d - 1) + 1 = r + d := by omega
    have : (i + 1) % d = (r + (d - 1) + 1) % d := by rw [e, Nat.add_mod_right, h']
    exact (Nat.ModEq.add_right_cancel' 1 this)
  rw [hf (i + 1) h1, zero_mul, zero_add]
  split_ifs with h
  · have h2 : (i - (d - 1)) % d ≠ r % d := by
      intro h'; apply hi
      have : i = (i - (d - 1)) + (d - 1) := by omega
      rw [this, Nat.add_mod, h', ← Nat.add_mod]
    rw [hf (i - (d - 1)) h2, mul_zero]
  · rw [mul_zero]

theorem natDegree_LopD_le (f : ℂ[X]) : (LopD d f).natDegree ≤ f.natDegree + (d - 1) := by
  unfold LopD
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_derivative_le f).trans (by omega)
  · rw [mul_assoc]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_mul_le.trans ?_
    have := natDegree_X_pow_le (R := ℂ) (d - 1)
    omega

theorem coeff_LopD_top (hd : 0 < d) (f : ℂ[X]) (n : ℕ) (hf : f.natDegree ≤ n) :
    (LopD d f).coeff (n + (d - 1)) = Complex.I * f.coeff n := by
  rw [LopD, coeff_add, coeff_derivative, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < n + (d - 1) + 1), zero_mul, zero_add,
    if_pos (by omega), show n + (d - 1) - (d - 1) = n by omega]

lemma tauD_congr {j r : ℕ} (h : j % d = r % d) : tauD d j = tauD d r := by
  unfold tauD; rw [h]

namespace FormHypD

variable (hB : FormHypD d B a)
include hB

theorem wt_orth (f g : ℂ[X]) (r s : ℕ) (hf : IsWtD d f r) (hg : IsWtD d g s)
    (hrs : r % d ≠ s % d) : B f g = 0 := by
  rw [hB.expand_left f g (f.natDegree + 1) (by omega)]
  refine sum_eq_zero fun i _ => ?_
  by_cases hi : i % d = r % d
  · rw [hB.expand_right g (X ^ i) (g.natDegree + 1) (by omega), sum_eq_zero, mul_zero]
    intro j _
    by_cases hj : j % d = s % d
    · rw [hB.weight i j (by rw [hi, hj]; exact hrs), mul_zero]
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
theorem ibp_wt (f g : ℂ[X]) (r : ℕ) (hg : IsWtD d g r) :
    B (LopD d f) g = -(tauD d r : ℂ) * a * B f (X * g) := by
  rw [hB.expand_right g (LopD d f) (g.natDegree + 1) (by omega), hB.mul_X_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j % d = r % d
  · rw [LopD, hB.ibp, tauD_congr hj]
    ring
  · rw [hg j hj, map_zero, zero_mul, zero_mul, mul_zero]

end FormHypD

namespace OPDataD

variable (hB : FormHypD d B a) (D : OPDataD d B)
include hB

omit hB in
theorem rhoSignD_ne_zero (hd : 0 < d) (n : ℕ) : rhoSignD d n ≠ 0 := by
  rw [rhoSignD_eq hd]; exact pow_ne_zero _ (by norm_num)

omit hB in
theorem norm_ne_zero (hd : 0 < d) (n : ℕ) : B (D.P n) (D.P n) ≠ 0 := by
  rw [D.norm]
  exact_mod_cast mul_ne_zero (rhoSignD_ne_zero hd n) (D.pos n).ne'

omit hB in
theorem coeff_self (n : ℕ) : (D.P n).coeff n = 1 := by
  have := D.monic n; rw [Monic, leadingCoeff, D.deg n] at this; exact this

theorem left_P (g : ℂ[X]) (n : ℕ) (hg : g.natDegree ≤ n) :
    B g (D.P n) = g.coeff n * B (X ^ n) (D.P n) := by
  rw [hB.expand_left g (D.P n) (n + 1) (by omega), sum_range_succ, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [hB.herm, D.orth n i (mem_range.mp hi), map_zero, mul_zero]

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

theorem vanish (hd : 0 < d) (g : ℂ[X]) (N : ℕ) (hg : g.natDegree ≤ N)
    (h0 : ∀ k ≤ N, B g (D.P k) = 0) : g = 0 := by
  by_contra hne
  have := extract hB D g g.natDegree le_rfl
  rw [h0 _ hg, coeff_natDegree] at this
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hne) (norm_ne_zero D hd _) this.symm

/-- Expansion in the orthogonal basis. -/
theorem expandP (hd : 0 < d) (g : ℂ[X]) (N : ℕ) (hg : g.natDegree ≤ N) :
    g = ∑ k ∈ range (N + 1), C (B g (D.P k) / B (D.P k) (D.P k)) * D.P k := by
  have hdeg : (∑ k ∈ range (N + 1), C (B g (D.P k) / B (D.P k) (D.P k)) * D.P k).natDegree ≤ N := by
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [D.deg]; exact Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hv := vanish hB D hd (g - ∑ k ∈ range (N + 1), C (B g (D.P k) / B (D.P k) (D.P k)) * D.P k) N
    ((natDegree_sub_le _ _).trans (max_le hg hdeg)) ?_
  · exact sub_eq_zero.mp hv
  · intro m hm
    rw [hB.sub_left, hB.sum_left, Finset.sum_eq_single m]
    · rw [hB.smul_left, div_mul_cancel₀ _ (norm_ne_zero D hd m), sub_self]
    · intro k _ hkm
      rw [hB.smul_left, P_P hB D k m, if_neg hkm, mul_zero]
    · intro h; exact absurd (mem_range.mpr (by omega)) h

end OPDataD

/-- Projection onto the weight space of `r`. -/
noncomputable def wprojD (d : ℕ) (f : ℂ[X]) (r : ℕ) : ℂ[X] :=
  ∑ i ∈ range (f.natDegree + 1), if i % d = r % d then C (f.coeff i) * X ^ i else 0

theorem coeff_wprojD (f : ℂ[X]) (r j : ℕ) :
    (wprojD d f r).coeff j = if j % d = r % d then f.coeff j else 0 := by
  unfold wprojD
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

theorem natDegree_wprojD_le (f : ℂ[X]) (r : ℕ) : (wprojD d f r).natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_wprojD]
  split_ifs
  · exact coeff_eq_zero_of_natDegree_lt hN
  · rfl

lemma tauD_sq (l : ℕ) : tauD d l * tauD d l = 1 := by
  unfold tauD; split_ifs
  · rw [← mul_pow]; norm_num
  · norm_num

theorem tauD_ne_zero (l : ℕ) : (tauD d l : ℂ) ≠ 0 := by
  have := tauD_sq (d := d) l
  intro h
  have h' : tauD d l = 0 := by exact_mod_cast h
  rw [h', zero_mul] at this; exact zero_ne_one this

theorem tauD_mul_self' (l : ℕ) : (tauD d l : ℂ) * tauD d l = 1 := by
  exact_mod_cast tauD_sq l

namespace FormHypD

variable (hB : FormHypD d B a)
include hB

theorem wprojD_X_pow (f : ℂ[X]) (r j : ℕ) :
    B (wprojD d f r) (X ^ j) = if j % d = r % d then B f (X ^ j) else 0 := by
  rw [hB.expand_left (wprojD d f r) _ (f.natDegree + 1)
    (lt_of_le_of_lt (natDegree_wprojD_le f r) (by omega))]
  split_ifs with hj
  · rw [hB.expand_left f (X ^ j) (f.natDegree + 1) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_wprojD]
    split_ifs with hi
    · rfl
    · rw [hB.weight i j (by rw [hj]; exact hi), mul_zero, mul_zero]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_wprojD]
    split_ifs with hi
    · rw [hB.weight i j (by rw [hi]; exact Ne.symm hj), mul_zero]
    · rw [zero_mul]

end FormHypD

namespace OPDataD

variable (hB : FormHypD d B a) (D : OPDataD d B)
include hB

theorem P_isWt (hd : 0 < d) (n : ℕ) : IsWtD d (D.P n) n := by
  have hQ : wprojD d (D.P n) n = D.P n := by
    have hv := vanish hB D hd (wprojD d (D.P n) n - D.P n) n ?_ ?_
    · exact sub_eq_zero.mp hv
    · refine (natDegree_sub_le _ _).trans (max_le ?_ (D.deg n).le)
      exact (natDegree_wprojD_le _ _).trans (D.deg n).le
    · intro k hk
      rw [hB.expand_right (D.P k) _ (k + 1) (by rw [D.deg]; omega)]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk := mem_range.mp hj
      rw [hB.sub_left, hB.wprojD_X_pow]
      split_ifs with hjn
      · rw [sub_self, mul_zero]
      · rw [D.orth n j (by
          by_contra hge
          push Not at hge
          rcases eq_or_lt_of_le hge with h | h
          · exact hjn (by rw [h])
          · omega), sub_zero, mul_zero]
  intro i hi
  rw [← hQ, coeff_wprojD, if_neg hi]

omit hB in
/-- Residues: equal residues and a gap less than `d` force equality. -/
lemma eq_of_mod_eq_of_lt {x y : ℕ} (hd : 0 < d) (h : x % d = y % d) (hxy : y ≤ x)
    (hlt : x < y + d) : x = y := by
  by_contra hne
  have hlt' : y < x := lt_of_le_of_ne hxy (Ne.symm hne)
  have hdvd : d ∣ x - y := (Nat.modEq_iff_dvd' hxy).mp h.symm
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Band structure of multiplication by `z`. -/
theorem band (hd : 0 < d) (ha : 0 < a) (n k : ℕ) (hk : k ≤ n) (hkd : k + (d - 1) ≠ n) :
    B (X * D.P n) (D.P k) = 0 := by
  by_cases hw : k % d = (n + 1) % d
  · have hibp := hB.ibp_wt (D.P k) (D.P n) n (P_isWt hB D hd n)
    have hlt : k + (d - 1) < n := by
      have hres : (k + (d - 1)) % d = n % d := by
        have e : k + (d - 1) + 1 = k + d := by omega
        have : (k + (d - 1) + 1) % d = (n + 1) % d := by rw [e, Nat.add_mod_right, hw]
        exact Nat.ModEq.add_right_cancel' 1 this
      by_contra hge
      push Not at hge
      exact hkd (eq_of_mod_eq_of_lt hd hres hge (by omega))
    rw [lower_left hB D (LopD d (D.P k)) n (by
      have := natDegree_LopD_le (d := d) (D.P k); rw [D.deg] at this; omega)] at hibp
    have hne : (-(tauD d n : ℂ) * a) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (tauD_ne_zero n)) (by exact_mod_cast ha.ne')
    have h0 : B (D.P k) (X * D.P n) = 0 := by
      rcases mul_eq_zero.mp hibp.symm with h | h
      · exact absurd h hne
      · exact h
    rw [hB.herm, h0, map_zero]
  · exact hB.wt_orth _ _ (n + 1) k (isWtD_X_mul (P_isWt hB D hd n)) (P_isWt hB D hd k)
      (fun h => hw h.symm)

end OPDataD

namespace OPDataD

/-- The lower coefficient `c_n = (i/a) 𝔥_n / 𝔥_{n+1-d}` (`0` for `n < d - 1`). -/
noncomputable def cc (D : OPDataD d B) (a : ℝ) (n : ℕ) : ℂ :=
  if d - 1 ≤ n then Complex.I / a * ((D.h n / D.h (n + 1 - d) : ℝ) : ℂ) else 0

/-- `ϱ(m + d - 1) = τ(m + d - 1) ϱ(m)`. -/
lemma rhoSignD_add (hd : 0 < d) (m : ℕ) :
    rhoSignD d (m + (d - 1)) = tauD d (m + (d - 1)) * rhoSignD d m := by
  have hfull : rhoSignD d (m + d) = -rhoSignD d m := by
    rw [rhoSignD_eq hd, rhoSignD_eq hd, Nat.add_mod_right, Nat.add_div_right _ hd, ← add_assoc,
      pow_succ]
    ring
  have hlast : rhoSignD d (m + d) = -tauD d (m + (d - 1)) * rhoSignD d (m + (d - 1)) := by
    unfold rhoSignD
    rw [show m + d = m + (d - 1) + 1 by omega, Finset.prod_range_succ]
    ring
  have hτ := tauD_sq (d := d) (m + (d - 1))
  rw [hlast] at hfull
  linear_combination (-tauD d (m + (d - 1))) * hfull - rhoSignD d (m + (d - 1)) * hτ

variable (hB : FormHypD d B a) (D : OPDataD d B)
include hB

theorem cformula (hd : 0 < d) (ha : 0 < a) (n : ℕ) (hn : d - 1 ≤ n) :
    B (X * D.P n) (D.P (n + 1 - d)) = D.cc a n * B (D.P (n + 1 - d)) (D.P (n + 1 - d)) := by
  have hibp := hB.ibp_wt (D.P (n + 1 - d)) (D.P n) n (P_isWt hB D hd n)
  have hL : B (LopD d (D.P (n + 1 - d))) (D.P n) = Complex.I * B (D.P n) (D.P n) := by
    rw [extract hB D _ n (by
      have := natDegree_LopD_le (d := d) (D.P (n + 1 - d)); rw [D.deg] at this; omega)]
    congr 1
    have := coeff_LopD_top hd (D.P (n + 1 - d)) (n + 1 - d) (D.deg _).le
    rw [show n + 1 - d + (d - 1) = n by omega, coeff_self, mul_one] at this
    exact this
  rw [hL] at hibp
  have hτ := tauD_mul_self' (d := d) n
  have hρ : rhoSignD d n = tauD d n * rhoSignD d (n + 1 - d) := by
    have := rhoSignD_add hd (n + 1 - d); rwa [show n + 1 - d + (d - 1) = n by omega] at this
  have hh3 : (D.h (n + 1 - d) : ℂ) ≠ 0 := by exact_mod_cast (D.pos (n + 1 - d)).ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hβ : B (D.P (n + 1 - d)) (X * D.P n) =
      -(Complex.I * ((rhoSignD d n * D.h n : ℝ) : ℂ)) * (tauD d n : ℂ) / a := by
    rw [D.norm] at hibp
    field_simp
    linear_combination (tauD d n : ℂ) * hibp - B (D.P (n + 1 - d)) (X * D.P n) * a * hτ
  rw [hB.herm, hβ, D.norm, cc, if_pos hn]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [hρ]
  push_cast
  field_simp
  linear_combination ((rhoSignD d (n + 1 - d) : ℂ) * (D.h n : ℂ)) * hτ

/-- `z P_n = P_{n+1} + c_n P_{n+1-d}` (`eq:polynomial-recurrences`). -/
theorem two_term (hd : 0 < d) (ha : 0 < a) (n : ℕ) :
    X * D.P n = D.P (n + 1) + C (D.cc a n) * D.P (n + 1 - d) := by
  have hv := vanish hB D hd (X * D.P n - D.P (n + 1) - C (D.cc a n) * D.P (n + 1 - d)) n ?_ ?_
  · linear_combination hv
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, coeff_sub, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (by rw [D.deg]; omega : (D.P (n + 1 - d)).natDegree < N),
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
    by_cases hkd : k + (d - 1) = n
    · have hn3 : n + 1 - d = k := by omega
      rw [← hn3, cformula hB D hd ha n (by omega), P_P hB D, if_pos rfl, sub_self]
    · rw [band hB D hd ha n k hk hkd, zero_sub, neg_eq_zero, P_P hB D]
      by_cases h3 : d - 1 ≤ n
      · rw [if_neg (by omega), mul_zero]
      · rw [cc, if_neg h3, zero_mul]

/-- Pairing `z P_k` with `P_m`. -/
theorem mulX_pair (hd : 0 < d) (ha : 0 < a) (k m : ℕ) :
    B (X * D.P k) (D.P m) =
      (if k + 1 = m then B (D.P m) (D.P m) else 0) +
        (if d - 1 ≤ k ∧ k + 1 - d = m then D.cc a k * B (D.P m) (D.P m) else 0) := by
  rw [two_term hB D hd ha k, hB.add_left, hB.smul_left, P_P hB D (k + 1) m, P_P hB D (k + 1 - d) m]
  congr 1
  by_cases h3 : d - 1 ≤ k <;> by_cases hm : k + 1 - d = m <;> simp [cc, h3, hm]

omit hB in
lemma cc_low (n : ℕ) (hn : n < d - 1) : D.cc a n = 0 := by
  unfold cc; rw [if_neg (by omega)]

/-- `B(z g, P_m)` through the expansion of `g` in the orthogonal basis. -/
theorem mulX_expand (hd : 0 < d) (ha : 0 < a) (g : ℂ[X]) (N : ℕ) (hg : g.natDegree ≤ N) (m : ℕ) :
    B (X * g) (D.P m) = ∑ k ∈ range (N + 1),
      B g (D.P k) / B (D.P k) (D.P k) * B (X * D.P k) (D.P m) := by
  conv_lhs => rw [expandP hB D hd g N hg]
  rw [Finset.mul_sum, hB.sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show X * (C (B g (D.P k) / B (D.P k) (D.P k)) * D.P k)
      = C (B g (D.P k) / B (D.P k) (D.P k)) * (X * D.P k) by ring, hB.smul_left]

/-- `S_j(n) = ∑_{s<j} c_{n+s}`. -/
noncomputable def Ssum (D : OPDataD d B) (a : ℝ) (n j : ℕ) : ℂ :=
  ∑ s ∈ range j, D.cc a (n + s)

/-- The remainder `T_j = z^j P_n - P_{n+j} - S_j P_{n+j-d}`. -/
noncomputable def Trem (D : OPDataD d B) (a : ℝ) (n j : ℕ) : ℂ[X] :=
  X ^ j * D.P n - D.P (n + j) - C (Ssum D a n j) * D.P (n + j - d)

omit hB in
lemma Ssum_low (n j : ℕ) (h : n + j < d) : Ssum D a n j = 0 := by
  unfold Ssum
  exact Finset.sum_eq_zero fun s hs => cc_low D (n + s) (by have := mem_range.mp hs; omega)

omit hB in
lemma natDegree_Trem (n j : ℕ) : (Trem D a n j).natDegree ≤ n + j := by
  unfold Trem
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_mul_le.trans ?_
    rw [D.deg]; have := natDegree_X_pow_le (R := ℂ) j; omega
  · rw [D.deg]
  · refine (natDegree_C_mul_le _ _).trans ?_
    rw [D.deg]; omega

/-- **Paths with one step `-(d-1)`**: `T_j ⊥ P_m` whenever `m + 2d > n + j`. -/
theorem Trem_orth (hd : 2 ≤ d) (ha : 0 < a) (n : ℕ) :
    ∀ j m, n + j < m + 2 * d → B (Trem D a n j) (D.P m) = 0 := by
  have hd0 : 0 < d := by omega
  intro j
  induction j with
  | zero =>
    intro m _
    unfold Trem Ssum
    simp only [pow_zero, one_mul, add_zero, sum_range_zero, map_zero, zero_mul, sub_zero, sub_self,
      hB.zero_left]
  | succ j ih =>
    intro m hm
    -- `T_{j+1} = X T_j + S_j c_{n+j-d} P_{n+j+1-2d}`
    have hstep : Trem D a n (j + 1) = X * Trem D a n j +
        C (Ssum D a n j * D.cc a (n + j - d)) * D.P (n + j - d + 1 - d) := by
      unfold Trem
      have hS : Ssum D a n (j + 1) = Ssum D a n j + D.cc a (n + j) := by
        unfold Ssum; rw [sum_range_succ]
      have e1 := two_term hB D hd0 ha (n + j)
      rw [show n + (j + 1) = n + j + 1 by ring, hS, pow_succ]
      by_cases hnj : d ≤ n + j
      · obtain ⟨p, hp⟩ : ∃ p, n + j = p + d := ⟨n + j - d, by omega⟩
        have e2 := two_term hB D hd0 ha p
        rw [show n + j - d = p by omega, show n + j + 1 - d = p + 1 by omega] at *
        rw [C_add, C_mul]
        linear_combination e1 + C (Ssum D a n j) * e2
      · have h0 : Ssum D a n j = 0 := Ssum_low D n j (by omega)
        simp only [h0, zero_add, zero_mul, map_zero, sub_zero, add_zero]
        linear_combination e1
    rw [hstep, hB.add_left, hB.smul_left,
      mulX_expand hB D hd0 ha (Trem D a n j) (n + j) (natDegree_Trem D n j) m]
    have hterm : ∀ k ∈ range (n + j + 1),
        B (Trem D a n j) (D.P k) / B (D.P k) (D.P k) * B (X * D.P k) (D.P m) = 0 := by
      intro k _
      by_cases hk : n + j < k + 2 * d
      · rw [ih k hk, zero_div, zero_mul]
      · rw [mulX_pair hB D hd0 ha k m, if_neg (by omega), if_neg (by omega), add_zero, mul_zero]
    rw [Finset.sum_eq_zero hterm, zero_add, P_P hB D]
    split_ifs with heq
    · -- the index `n + j - d + 1 - d = m` forces `c_{n+j-d} = 0`
      have hc : D.cc a (n + j - d) = 0 := cc_low D _ (by omega)
      rw [hc, mul_zero, zero_mul]
    · rw [mul_zero]

/-- The coefficient of `P_{n-1}` in `z^{d-1} P_n` (`eq:polynomial-recurrences`, paths). -/
theorem Xpow_pair (hd : 2 ≤ d) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    B (X ^ (d - 1) * D.P n) (D.P (n - 1)) = Ssum D a n (d - 1) * B (D.P (n - 1)) (D.P (n - 1)) := by
  have hT := Trem_orth hB D hd ha n (d - 1) (n - 1) (by omega)
  unfold Trem at hT
  rw [hB.sub_left, hB.sub_left, hB.smul_left, P_P hB D, if_neg (by omega),
    show n + (d - 1) - d = n - 1 by omega, P_P hB D, if_pos rfl] at hT
  linear_combination hT

/-- The complex form of the recurrence. -/
theorem rec_complex (hd : 2 ≤ d) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) * B (D.P (n - 1)) (D.P (n - 1)) +
        Complex.I * (Ssum D a n (d - 1) * B (D.P (n - 1)) (D.P (n - 1))) =
      -(tauD d (n - 1) : ℂ) * a * B (D.P n) (D.P n) := by
  have hd0 : 0 < d := by omega
  have hibp := hB.ibp_wt (D.P n) (D.P (n - 1)) (n - 1) (P_isWt hB D hd0 (n - 1))
  have hX : X * D.P (n - 1) = D.P n + C (D.cc a (n - 1)) * D.P (n - d) := by
    have := two_term hB D hd0 ha (n - 1); rwa [show n - 1 + 1 = n by omega] at this
  rw [hX, hB.add_right, hB.smul_right, P_P hB D n (n - d), if_neg (by omega), mul_zero,
    add_zero] at hibp
  rw [← hibp, LopD, hB.add_left, mul_assoc, hB.smul_left, Xpow_pair hB D hd ha n hn,
    extract hB D (derivative (D.P n)) (n - 1)
      ((natDegree_derivative_le _).trans (by rw [D.deg]))]
  congr 1
  rw [coeff_derivative, show n - 1 + 1 = n by omega, coeff_self, one_mul]
  push_cast [Nat.cast_sub hn]
  ring

/-- The real recurrence on the signed norms (`eq:FH-recurrence` before normalization):
`(m+1) 𝔥_m - a⁻¹ ∑_{s<d-1} [d-1 ≤ m+1+s] 𝔥_{m+1+s}/𝔥_{m+s+2-d} 𝔥_m = a 𝔥_{m+1}`. -/
theorem rec_real (hd : 2 ≤ d) (ha : 0 < a) (m : ℕ) :
    ((m : ℝ) + 1) * D.h m - (1 / a) * (∑ s ∈ range (d - 1),
        (if d - 1 ≤ m + 1 + s then D.h (m + 1 + s) / D.h (m + 1 + s + 1 - d) else 0)) * D.h m
      = a * D.h (m + 1) := by
  have hd0 : 0 < d := by omega
  have hc := rec_complex hB D hd ha (m + 1) (by omega)
  simp only [show m + 1 - 1 = m by omega] at hc
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hII : ∀ k : ℕ, Complex.I * D.cc a k =
      -(((if d - 1 ≤ k then D.h k / D.h (k + 1 - d) else 0 : ℝ) : ℂ) / a) := by
    intro k
    unfold cc
    split_ifs
    · push_cast; field_simp; rw [Complex.I_sq]; ring
    · simp
  have hsum : Complex.I * (Ssum D a (m + 1) (d - 1) * B (D.P m) (D.P m))
      = (∑ s ∈ range (d - 1), Complex.I * D.cc a (m + 1 + s)) * B (D.P m) (D.P m) := by
    unfold Ssum
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hsum] at hc
  simp_rw [hII] at hc
  rw [D.norm, D.norm] at hc
  have hstep : rhoSignD d (m + 1) = -tauD d m * rhoSignD d m := by
    unfold rhoSignD; rw [Finset.prod_range_succ]; ring
  rw [hstep] at hc
  have hτ : (tauD d m : ℂ) * tauD d m = 1 := tauD_mul_self' m
  have hρ0 : (rhoSignD d m : ℂ) ≠ 0 := by exact_mod_cast rhoSignD_ne_zero hd0 m
  set A : ℝ := ∑ s ∈ range (d - 1),
    (if d - 1 ≤ m + 1 + s then D.h (m + 1 + s) / D.h (m + 1 + s + 1 - d) else 0) with hA
  have hAc : (∑ s ∈ range (d - 1), -(((if d - 1 ≤ m + 1 + s then
      D.h (m + 1 + s) / D.h (m + 1 + s + 1 - d) else 0 : ℝ) : ℂ) / a)) = -((A : ℂ) / a) := by
    rw [hA, Finset.sum_neg_distrib, Complex.ofReal_sum, Finset.sum_div]
  rw [hAc] at hc
  have key : (rhoSignD d m : ℂ) * ((((m : ℝ) + 1) * D.h m - (1 / a) * A * D.h m : ℝ) - a * D.h (m + 1))
      = 0 := by
    push_cast at hc ⊢
    field_simp at hc ⊢
    linear_combination (rhoSignD d m : ℂ) * hc + (rhoSignD d m : ℂ) * (a : ℂ) ^ 2 * (D.h (m + 1) : ℂ) * hτ
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hρ0
  · have := sub_eq_zero.mp h
    exact_mod_cast this

end OPDataD

end Painleve
