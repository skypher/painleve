import Painleve.Signs
import Painleve.Moments
import Painleve.OrthoPoly
open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

theorem pairing_X_pow (a : ℝ) (p q : ℕ) :
    pairing a (X ^ p) (X ^ q) =
      (-1 : ℂ) ^ (q % 4 + q / 4) * ∫ z : ℂ, z ^ p * conj z ^ q * density a z := by
  unfold pairing
  rw [twist_X_pow, ← integral_const_mul]
  congr 1
  funext z
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem pairing_X_pow_eq_zero (a : ℝ) (p q : ℕ) (h : p % 4 ≠ q % 4) :
    pairing a (X ^ p) (X ^ q) = 0 := by
  rw [pairing_X_pow, moment_eq_zero_of_mod_ne a p q h, mul_zero]

theorem integrable_pair (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    Integrable (fun z : ℂ => f.eval z * conj (g.eval z) * density a z) := by
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 =>
    simp only [eval_add, add_mul]
    exact h1.add h2
  | monomial n c =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 =>
      simp only [eval_add, map_add, mul_add, add_mul]
      exact h1.add h2
    | monomial m d =>
      have e : (fun z : ℂ => (monomial n c).eval z * conj ((monomial m d).eval z) * density a z)
          = fun z => (c * conj d) * (z ^ n * conj z ^ m * density a z) := by
        funext z
        simp only [eval_monomial, map_mul, map_pow]
        ring
      rw [e]
      exact (integrable_moment a ha n m).const_mul _

theorem pairing_add_left (a : ℝ) (ha : 0 < a) (f1 f2 g : ℂ[X]) :
    pairing a (f1 + f2) g = pairing a f1 g + pairing a f2 g := by
  unfold pairing
  simp only [eval_add, add_mul]
  exact integral_add (integrable_pair a ha f1 (twist g)) (integrable_pair a ha f2 (twist g))

theorem pairing_add_right (a : ℝ) (ha : 0 < a) (f g1 g2 : ℂ[X]) :
    pairing a f (g1 + g2) = pairing a f g1 + pairing a f g2 := by
  unfold pairing
  rw [twist_add]
  simp only [eval_add, map_add, mul_add, add_mul]
  exact integral_add (integrable_pair a ha f (twist g1)) (integrable_pair a ha f (twist g2))

theorem pairing_C_mul_left (a : ℝ) (c : ℂ) (f g : ℂ[X]) :
    pairing a (C c * f) g = c * pairing a f g := by
  unfold pairing
  rw [← integral_const_mul]
  congr 1
  funext z
  simp only [eval_mul, eval_C]
  ring

theorem pairing_C_mul_right (a : ℝ) (d : ℂ) (f g : ℂ[X]) :
    pairing a f (C d * g) = conj d * pairing a f g := by
  unfold pairing
  rw [twist_C_mul, ← integral_const_mul]
  congr 1
  funext z
  simp only [eval_mul, eval_C, map_mul]
  ring

theorem pairing_left_sum (a : ℝ) (ha : 0 < a) (f : ℂ[X]) (q : ℕ) :
    pairing a f (X ^ q) = f.sum fun p c => c * pairing a (X ^ p) (X ^ q) := by
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 =>
    rw [pairing_add_left a ha, h1, h2, sum_add_index]
    all_goals simp [add_mul]
  | monomial p c =>
    rw [sum_monomial_index, ← C_mul_X_pow_eq_monomial, pairing_C_mul_left a c]
    all_goals simp

theorem pairing_right_sum (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    pairing a f g = g.sum fun q d => conj d * pairing a f (X ^ q) := by
  induction g using Polynomial.induction_on' with
  | add g1 g2 h1 h2 =>
    rw [pairing_add_right a ha, h1, h2, sum_add_index]
    all_goals simp [add_mul]
  | monomial q d =>
    rw [sum_monomial_index, ← C_mul_X_pow_eq_monomial, pairing_C_mul_right]
    all_goals simp

theorem pairing_eq_sform (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    pairing a f g = sform (fun p q => pairing a (X ^ p) (X ^ q)) f g := by
  rw [sform_eq_sum_right, pairing_right_sum a ha f g]
  congr 1
  funext q d
  rw [sform_X_pow_right, pairing_left_sum a ha f q]

noncomputable def blockGram (a : ℝ) (r k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  fun p q => pairing a (X ^ (r + 4 * (p : ℕ))) (X ^ (r + 4 * (q : ℕ)))

theorem gramLead_eq_gramM (a : ℝ) (n : ℕ) :
    gramLead a n = gramM (fun p q => pairing a (X ^ p) (X ^ q)) n := rfl

theorem det_gramLead_eq_prod (a : ℝ) (n : ℕ) :
    (gramLead a n).det = ∏ r : Fin 4, (blockGram a r ((n + 3 - r) / 4)).det := by
  set b : Fin n → Fin 4 := fun i => ⟨(i : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ with hb
  have hBT : Matrix.BlockTriangular (gramLead a n) b := by
    intro i j hij
    show pairing a (X ^ (i : ℕ)) (X ^ (j : ℕ)) = 0
    apply pairing_X_pow_eq_zero
    intro h
    have hbe : b i = b j := Fin.ext h
    rw [hbe] at hij
    exact lt_irrefl _ hij
  rw [Matrix.BlockTriangular.det_fintype hBT]
  refine Finset.prod_congr rfl fun r _ => ?_
  have hr4 : (r : ℕ) < 4 := r.isLt
  have hf : ∀ p : Fin ((n + 3 - (r : ℕ)) / 4), (r : ℕ) + 4 * (p : ℕ) < n := fun p => by
    have := p.isLt
    omega
  have hfb : ∀ p : Fin ((n + 3 - (r : ℕ)) / 4), b ⟨(r : ℕ) + 4 * (p : ℕ), hf p⟩ = r :=
    fun p => Fin.ext (by
      show ((r : ℕ) + 4 * (p : ℕ)) % 4 = (r : ℕ)
      omega)
  let F : Fin ((n + 3 - (r : ℕ)) / 4) → {i : Fin n // b i = r} :=
    fun p => ⟨⟨(r : ℕ) + 4 * (p : ℕ), hf p⟩, hfb p⟩
  have hF : Function.Bijective F := by
    constructor
    · intro p q h
      have h1 : (r : ℕ) + 4 * (p : ℕ) = (r : ℕ) + 4 * (q : ℕ) :=
        congrArg (fun x => (x.1.1 : ℕ)) h
      exact Fin.ext (by omega)
    · rintro ⟨⟨i, hi⟩, hbi⟩
      have h2 : i % 4 = (r : ℕ) := congrArg Fin.val hbi
      refine ⟨⟨i / 4, by omega⟩, ?_⟩
      exact Subtype.ext (Fin.ext (by show (r : ℕ) + 4 * (i / 4) = i; omega))
  let e := Equiv.ofBijective F hF
  have hmat : blockGram a r ((n + 3 - (r : ℕ)) / 4)
      = ((gramLead a n).toSquareBlock b r).submatrix e e := by
    ext p q
    rfl
  rw [hmat, Matrix.det_submatrix_equiv_self]

end Painleve
