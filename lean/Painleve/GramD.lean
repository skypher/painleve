import Painleve.StatementD
import Painleve.BlockAlg
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The Gram form for general `d` (Section 2 of `paper.tex`)

The twist on monomials (`eq:twist-sign`), orthogonality of distinct weight
spaces, the block decomposition of the leading Gram determinants, and the
scaling `Δ_k^{(r)} = (-1)^{rk} d^{2·binom(k,2)} det[(i/d)^{p+q} M_{pq}^{(r)}]`
(first step of `cor:hankel`).
-/

open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

variable {d : ℕ}

theorem etaD_pow (hd : 0 < d) : etaD d ^ d = -1 := by
  unfold etaD
  rw [← Complex.exp_nat_mul]
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h : (d : ℂ) * (↑Real.pi * I / d) = ↑Real.pi * I := by field_simp
  rw [h, Complex.exp_pi_mul_I]

theorem etaD_ne_zero : etaD d ≠ 0 := Complex.exp_ne_zero _

lemma norm_etaD : ‖etaD d‖ = 1 := by
  unfold etaD
  rw [Complex.norm_exp]
  simp [Complex.div_re]

/-- `(-η)^{-r} η^{r+dq} = (-1)^{r+q}`. -/
theorem twistD_key (hd : 0 < d) (r q : ℕ) :
    (-etaD d) ^ (-((r : ℕ) : ℤ)) * etaD d ^ (r + d * q) = (-1 : ℂ) ^ (r + q) := by
  have hne : etaD d ≠ 0 := etaD_ne_zero
  have hs : ((-1 : ℂ) ^ r) * ((-1 : ℂ) ^ r) = 1 := by rw [← mul_pow]; norm_num
  have hinv : ((-1 : ℂ) ^ r)⁻¹ = (-1 : ℂ) ^ r := inv_eq_of_mul_eq_one_right hs
  have he : etaD d ^ r ≠ 0 := pow_ne_zero _ hne
  have hneg : (-etaD d) ^ (-((r : ℕ) : ℤ)) = ((-1 : ℂ) ^ r * etaD d ^ r)⁻¹ := by
    rw [zpow_neg, zpow_natCast, neg_pow]
  rw [hneg, pow_add, pow_mul, etaD_pow hd, mul_inv, hinv, pow_add]
  field_simp

theorem twistD_monomial (n : ℕ) (c : ℂ) :
    twistD d (monomial n c) = monomial n (c * ((-etaD d) ^ (-((n % d : ℕ) : ℤ)) * etaD d ^ n)) := by
  unfold twistD
  rw [sum_monomial_index]
  · congr 1; ring
  · simp

theorem twistD_add (f g : ℂ[X]) : twistD d (f + g) = twistD d f + twistD d g := by
  unfold twistD
  apply sum_add_index
  · intro i; simp
  · intro i b₁ b₂; simp [add_mul]

theorem twistD_X_pow (hd : 0 < d) (m : ℕ) :
    twistD d (X ^ m) = C ((-1 : ℂ) ^ (m % d + m / d)) * X ^ m := by
  simp only [X_pow_eq_monomial]
  rw [twistD_monomial, C_mul_monomial]
  congr 1
  have h := twistD_key hd (m % d) (m / d)
  rw [Nat.mod_add_div] at h
  rw [one_mul, mul_one, h]

theorem twistD_C_mul (c : ℂ) (f : ℂ[X]) : twistD d (C c * f) = C c * twistD d f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, twistD_add, twistD_add, hp, hq, mul_add]
  | monomial n b => simp only [C_mul_monomial, twistD_monomial, mul_assoc]

/-! ### The density -/

lemma conj_pow_add_real (z : ℂ) : ∃ r : ℝ, z ^ d + conj z ^ d = (r : ℂ) := by
  refine ⟨(z ^ d + conj z ^ d).re, ?_⟩
  have hc : conj (z ^ d + conj z ^ d) = z ^ d + conj z ^ d := by
    simp only [map_add, map_pow, conj_conj]; ring
  exact (Complex.conj_eq_iff_re.mp hc).symm

theorem norm_densityD (a : ℝ) (z : ℂ) : ‖densityD d a z‖ = Real.exp (-a * ‖z‖ ^ 2) := by
  unfold densityD
  rw [Complex.norm_exp]
  congr 1
  obtain ⟨r, hr⟩ := conj_pow_add_real (d := d) z
  rw [hr]
  have h4 : (I / d) * (r : ℂ) = ((r / d : ℝ) : ℂ) * I := by push_cast; ring
  rw [h4]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_im]
  ring

theorem integrable_momentD (a : ℝ) (ha : 0 < a) (p q : ℕ) :
    Integrable (fun z : ℂ => z ^ p * conj z ^ q * densityD d a z) := by
  obtain ⟨C, hC⟩ := poly_gauss a ha (p + q)
  refine Integrable.mono' ((integrable_gauss a ha).const_mul C) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold densityD
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_densityD, ← pow_add]
    exact hC ‖z‖ (norm_nonneg z)

lemma densityD_rot (a : ℝ) (ω : ℂ) (hω : ω ^ d = 1) (hn : ‖ω‖ = 1) (z : ℂ) :
    densityD d a (ω * z) = densityD d a z := by
  unfold densityD
  have hc : conj ω ^ d = 1 := by rw [← map_pow, hω, map_one]
  rw [norm_mul, hn, one_mul, mul_pow, hω, one_mul, map_mul, mul_pow, hc, one_mul]

lemma densityD_eta_mul (hd : 0 < d) (a : ℝ) (z : ℂ) :
    densityD d a (etaD d * z) = conj (densityD d a z) := by
  unfold densityD
  rw [← Complex.exp_conj]
  congr 1
  have h1 : ‖etaD d * z‖ = ‖z‖ := by rw [norm_mul, norm_etaD, one_mul]
  have h2 : (etaD d * z) ^ d = -z ^ d := by rw [mul_pow, etaD_pow hd]; ring
  have hc : conj (etaD d) ^ d = -1 := by rw [← map_pow, etaD_pow hd, map_neg, map_one]
  have h3 : conj (etaD d * z) ^ d = -conj z ^ d := by rw [map_mul, mul_pow, hc]; ring
  rw [h1, h2, h3]
  simp only [map_add, map_mul, map_neg, map_div₀, map_pow, conj_ofReal, conj_I, conj_conj,
    map_natCast]
  ring

/-- Distinct weights are orthogonal (rotation by a primitive `d`-th root of unity). -/
theorem momentD_eq_zero_of_mod_ne (hd : 0 < d) (a : ℝ) (p q : ℕ) (h : p % d ≠ q % d) :
    ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z = 0 := by
  set ω : ℂ := Complex.exp (2 * Real.pi * I / d) with hωdef
  have hprim : IsPrimitiveRoot ω d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hωd : ω ^ d = 1 := hprim.pow_eq_one
  have hωn : ‖ω‖ = 1 := by
    rw [hωdef, Complex.norm_exp]; simp [Complex.div_re]
  have hconj : conj ω = ω ^ (d - 1) := by
    have hmul : ω * conj ω = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hωn]; norm_num
    have hmul' : ω * ω ^ (d - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hωd]
    have hne : ω ≠ 0 := by intro h0; rw [h0, norm_zero] at hωn; norm_num at hωn
    exact mul_left_cancel₀ hne (hmul.trans hmul'.symm)
  have h1 : ∫ z : ℂ, (ω * z) ^ p * conj (ω * z) ^ q * densityD d a (ω * z)
      = ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z :=
    integral_rot_unit ω hωn (fun z => z ^ p * conj z ^ q * densityD d a z)
  have h2 : ∀ z : ℂ, (ω * z) ^ p * conj (ω * z) ^ q * densityD d a (ω * z)
      = ω ^ (p + (d - 1) * q) * (z ^ p * conj z ^ q * densityD d a z) := by
    intro z
    rw [densityD_rot a ω hωd hωn, map_mul, hconj, mul_pow, mul_pow, pow_add, ← pow_mul]
    ring
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  have hc1 : ω ^ (p + (d - 1) * q) ≠ 1 := by
    intro h1'
    have hdvd := (hprim.pow_eq_one_iff_dvd _).mp h1'
    apply h
    have h0 : (p + (d - 1) * q) % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hdq : d * q = (d - 1) * q + q := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hd]
    calc p % d = (p + d * q) % d := (Nat.add_mul_mod_self_left p d q).symm
      _ = ((p + (d - 1) * q) + q) % d := by rw [hdq, Nat.add_assoc]
      _ = q % d := by rw [Nat.add_mod, h0, zero_add, Nat.mod_mod]
  have hz : (1 - ω ^ (p + (d - 1) * q)) * ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z = 0 := by
    linear_combination (-1 : ℂ) * h1
  rcases mul_eq_zero.mp hz with h4 | h4
  · exact absurd (sub_eq_zero.mp h4).symm hc1
  · exact h4

/-! ### The pairing on monomials and its bilinearity -/

theorem pairingD_X_pow (hd : 0 < d) (a : ℝ) (p q : ℕ) :
    pairingD d a (X ^ p) (X ^ q) =
      (-1 : ℂ) ^ (q % d + q / d) * ∫ z : ℂ, z ^ p * conj z ^ q * densityD d a z := by
  unfold pairingD
  rw [twistD_X_pow hd, ← integral_const_mul]
  congr 1
  funext z
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem pairingD_X_pow_eq_zero (hd : 0 < d) (a : ℝ) (p q : ℕ) (h : p % d ≠ q % d) :
    pairingD d a (X ^ p) (X ^ q) = 0 := by
  rw [pairingD_X_pow hd, momentD_eq_zero_of_mod_ne hd a p q h, mul_zero]

theorem integrable_pairD (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    Integrable (fun z : ℂ => f.eval z * conj (g.eval z) * densityD d a z) := by
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 => simp only [eval_add, add_mul]; exact h1.add h2
  | monomial n c =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 => simp only [eval_add, map_add, mul_add, add_mul]; exact h1.add h2
    | monomial m b =>
      have e : (fun z : ℂ => (monomial n c).eval z * conj ((monomial m b).eval z) *
          densityD d a z) = fun z => (c * conj b) * (z ^ n * conj z ^ m * densityD d a z) := by
        funext z; simp only [eval_monomial, map_mul, map_pow]; ring
      rw [e]
      exact (integrable_momentD a ha n m).const_mul _

theorem pairingD_add_left (a : ℝ) (ha : 0 < a) (f1 f2 g : ℂ[X]) :
    pairingD d a (f1 + f2) g = pairingD d a f1 g + pairingD d a f2 g := by
  unfold pairingD
  simp only [eval_add, add_mul]
  exact integral_add (integrable_pairD a ha f1 (twistD d g)) (integrable_pairD a ha f2 (twistD d g))

theorem pairingD_add_right (a : ℝ) (ha : 0 < a) (f g1 g2 : ℂ[X]) :
    pairingD d a f (g1 + g2) = pairingD d a f g1 + pairingD d a f g2 := by
  unfold pairingD
  rw [twistD_add]
  simp only [eval_add, map_add, mul_add, add_mul]
  exact integral_add (integrable_pairD a ha f (twistD d g1)) (integrable_pairD a ha f (twistD d g2))

theorem pairingD_C_mul_left (a : ℝ) (c : ℂ) (f g : ℂ[X]) :
    pairingD d a (C c * f) g = c * pairingD d a f g := by
  unfold pairingD
  rw [← integral_const_mul]
  congr 1; funext z; simp only [eval_mul, eval_C]; ring

theorem pairingD_C_mul_right (a : ℝ) (b : ℂ) (f g : ℂ[X]) :
    pairingD d a f (C b * g) = conj b * pairingD d a f g := by
  unfold pairingD
  rw [twistD_C_mul, ← integral_const_mul]
  congr 1; funext z; simp only [eval_mul, eval_C, map_mul]; ring

theorem pairingD_left_sum (a : ℝ) (ha : 0 < a) (f : ℂ[X]) (q : ℕ) :
    pairingD d a f (X ^ q) = f.sum fun p c => c * pairingD d a (X ^ p) (X ^ q) := by
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 =>
    rw [pairingD_add_left a ha, h1, h2, sum_add_index]
    all_goals simp [add_mul]
  | monomial p c =>
    rw [sum_monomial_index, ← C_mul_X_pow_eq_monomial, pairingD_C_mul_left a c]
    all_goals simp

theorem pairingD_right_sum (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    pairingD d a f g = g.sum fun q b => conj b * pairingD d a f (X ^ q) := by
  induction g using Polynomial.induction_on' with
  | add g1 g2 h1 h2 =>
    rw [pairingD_add_right a ha, h1, h2, sum_add_index]
    all_goals simp [add_mul]
  | monomial q b =>
    rw [sum_monomial_index, ← C_mul_X_pow_eq_monomial, pairingD_C_mul_right]
    all_goals simp

theorem pairingD_eq_sform (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    pairingD d a f g = sform (fun p q => pairingD d a (X ^ p) (X ^ q)) f g := by
  rw [sform_eq_sum_right, pairingD_right_sum a ha f g]
  congr 1
  funext q b
  rw [sform_X_pow_right, pairingD_left_sum a ha f q]

theorem gramLeadD_eq_gramM (a : ℝ) (n : ℕ) :
    gramLeadD d a n = gramM (fun p q => pairingD d a (X ^ p) (X ^ q)) n := rfl

/-! ### Block decomposition -/

/-- The Gram block `G^{(r)}` of size `k` (`eq:gram-block`). -/
noncomputable def blockGramD (d : ℕ) (a : ℝ) (r k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  fun p q => pairingD d a (X ^ (r + d * (p : ℕ))) (X ^ (r + d * (q : ℕ)))

theorem det_gramLeadD_eq_prod (hd : 0 < d) (a : ℝ) (n : ℕ) :
    (gramLeadD d a n).det = ∏ r : Fin d, (blockGramD d a r ((n + d - 1 - r) / d)).det := by
  set b : Fin n → Fin d := fun i => ⟨(i : ℕ) % d, Nat.mod_lt _ hd⟩ with hb
  have hBT : Matrix.BlockTriangular (gramLeadD d a n) b := by
    intro i j hij
    show pairingD d a (X ^ (i : ℕ)) (X ^ (j : ℕ)) = 0
    apply pairingD_X_pow_eq_zero hd
    intro h
    have hbe : b i = b j := Fin.ext h
    rw [hbe] at hij
    exact lt_irrefl _ hij
  rw [Matrix.BlockTriangular.det_fintype hBT]
  refine Finset.prod_congr rfl fun r _ => ?_
  have hrd : (r : ℕ) < d := r.isLt
  have hf : ∀ p : Fin ((n + d - 1 - (r : ℕ)) / d), (r : ℕ) + d * (p : ℕ) < n := fun p => by
    have h1 : (p : ℕ) + 1 ≤ (n + d - 1 - (r : ℕ)) / d := p.isLt
    rw [Nat.le_div_iff_mul_le hd, Nat.succ_mul] at h1
    rw [mul_comm d]
    generalize (p : ℕ) * d = m at h1 ⊢
    omega
  have hfb : ∀ p : Fin ((n + d - 1 - (r : ℕ)) / d), b ⟨(r : ℕ) + d * (p : ℕ), hf p⟩ = r :=
    fun p => Fin.ext (by
      show ((r : ℕ) + d * (p : ℕ)) % d = (r : ℕ)
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrd])
  let F : Fin ((n + d - 1 - (r : ℕ)) / d) → {i : Fin n // b i = r} :=
    fun p => ⟨⟨(r : ℕ) + d * (p : ℕ), hf p⟩, hfb p⟩
  have hF : Function.Bijective F := by
    constructor
    · intro p q h
      have h1 : (r : ℕ) + d * (p : ℕ) = (r : ℕ) + d * (q : ℕ) :=
        congrArg (fun x => (x.1.1 : ℕ)) h
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel h1))
    · rintro ⟨⟨i, hi⟩, hbi⟩
      have h2 : i % d = (r : ℕ) := congrArg Fin.val hbi
      have hidx : i / d < (n + d - 1 - (r : ℕ)) / d := by
        rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hd, Nat.succ_mul]
        have h3 := Nat.div_add_mod i d
        rw [h2, mul_comm] at h3
        generalize i / d * d = m at h3 ⊢
        omega
      refine ⟨⟨i / d, hidx⟩, ?_⟩
      exact Subtype.ext (Fin.ext (by
        show (r : ℕ) + d * (i / d) = i
        rw [← h2]; exact Nat.mod_add_div i d))
  let e := Equiv.ofBijective F hF
  have hmat : blockGramD d a r ((n + d - 1 - (r : ℕ)) / d)
      = ((gramLeadD d a n).toSquareBlock b r).submatrix e e := by
    ext p q; rfl
  rw [hmat, Matrix.det_submatrix_equiv_self]

/-- Weighted planar moments `M_{kl}^{(r)}` (`eq:gram-block`). -/
noncomputable def wmomD (d : ℕ) (a : ℝ) (r k l : ℕ) : ℂ :=
  ∫ z : ℂ, ((‖z‖ ^ (2 * r) : ℝ) : ℂ) * z ^ (d * k) * conj z ^ (d * l) * densityD d a z

theorem blockGramD_apply (hd : 0 < d) (a : ℝ) (r k : ℕ) (hr : r < d) (p q : Fin k) :
    blockGramD d a r k p q = (-1 : ℂ) ^ (r + (q : ℕ)) * wmomD d a r p q := by
  unfold blockGramD wmomD
  rw [pairingD_X_pow hd]
  have h1 : (r + d * (q : ℕ)) % d = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : (r + d * (q : ℕ)) / d = q := by
    rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, zero_add]
  rw [h1, h2]
  congr 1
  congr 1
  funext z
  rw [pow_add, pow_add, cast_norm_pow_two_mul z r]
  ring

theorem det_blockGramD (hd : 0 < d) (a : ℝ) (r k : ℕ) (hr : r < d) :
    (blockGramD d a r k).det =
      (-1 : ℂ) ^ (r * k) * ((d : ℂ) ^ 2) ^ (k * (k - 1) / 2) *
        (Matrix.of fun p q : Fin k => (I / d) ^ ((p : ℕ) + q) * wmomD d a r p q).det := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hcI : ((d : ℂ) / I) * (I / d) = (1 : ℂ) := by field_simp
  have hc2 : ((d : ℂ) / I) * ((d : ℂ) / I) = -((d : ℂ) ^ 2) := by
    rw [show ((d : ℂ) / I) * ((d : ℂ) / I) = (d : ℂ) ^ 2 / (I * I) by ring, Complex.I_mul_I]
    ring
  have hB : blockGramD d a r k = ((-1 : ℂ) ^ r) •
      (Matrix.of fun p q : Fin k =>
        ((d : ℂ) / I) ^ (p : ℕ) *
          (Matrix.of fun p q : Fin k => (I / d) ^ ((p : ℕ) + q) * wmomD d a r p q) p q *
          ((-1 : ℂ) ^ (q : ℕ) * ((d : ℂ) / I) ^ (q : ℕ))) := by
    ext p q
    rw [blockGramD_apply hd a r k hr p q]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have key : ((d : ℂ) / I) ^ ((p : ℕ) + q) * (I / d) ^ ((p : ℕ) + q) = 1 := by
      rw [← mul_pow, hcI, one_pow]
    have hsplit : ((d : ℂ) / I) ^ (p : ℕ) * ((d : ℂ) / I) ^ (q : ℕ)
        = ((d : ℂ) / I) ^ ((p : ℕ) + q) := (pow_add _ _ _).symm
    rw [pow_add]
    linear_combination ((-1 : ℂ) ^ r * (-1 : ℂ) ^ (q : ℕ) * wmomD d a r p q) * (-1 : ℂ) * key
      + ((-1 : ℂ) ^ r * (-1 : ℂ) ^ (q : ℕ) * wmomD d a r p q * (I / d) ^ ((p : ℕ) + q))
        * (-1 : ℂ) * hsplit
  rw [hB, Matrix.det_smul, Fintype.card_fin, det_row_col_scale, Finset.prod_mul_distrib,
    prod_fin_pow_val, prod_fin_pow_val, ← pow_mul]
  have e1 : ((d : ℂ) / I) ^ (k * (k - 1) / 2) * ((d : ℂ) / I) ^ (k * (k - 1) / 2)
      = (-((d : ℂ) ^ 2)) ^ (k * (k - 1) / 2) := by rw [← mul_pow, hc2]
  have e2 : (-((d : ℂ) ^ 2)) ^ (k * (k - 1) / 2)
      = (-1) ^ (k * (k - 1) / 2) * ((d : ℂ) ^ 2) ^ (k * (k - 1) / 2) := by
    rw [show (-((d : ℂ) ^ 2)) = (-1) * (d : ℂ) ^ 2 by ring, mul_pow]
  have e3 : (-1 : ℂ) ^ (k * (k - 1) / 2) * (-1) ^ (k * (k - 1) / 2) = 1 := by
    rw [← mul_pow]; norm_num
  have hS : ((d : ℂ) / I) ^ (k * (k - 1) / 2) *
      ((-1) ^ (k * (k - 1) / 2) * ((d : ℂ) / I) ^ (k * (k - 1) / 2))
      = ((d : ℂ) ^ 2) ^ (k * (k - 1) / 2) := by
    linear_combination (-1 : ℂ) ^ (k * (k - 1) / 2) * e1 + (-1 : ℂ) ^ (k * (k - 1) / 2) * e2
      + ((d : ℂ) ^ 2) ^ (k * (k - 1) / 2) * e3
  linear_combination ((-1 : ℂ) ^ (r * k) * (Matrix.of fun p q : Fin k => (I / d) ^ ((p : ℕ) + q) *
    wmomD d a r p q).det) * hS

end Painleve
