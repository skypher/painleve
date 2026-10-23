import Painleve.Gram
import Mathlib.Algebra.Polynomial.Derivative
open Complex Polynomial MeasureTheory
open scoped ComplexConjugate

namespace Painleve

/-- Sign bookkeeping: `conj(η)^p η^q = (-1)^{...}` when `p ≡ q (mod 4)`. -/
theorem sign_herm (p q : ℕ) (h : p % 4 = q % 4) :
    (-1 : ℂ) ^ (p % 4 + p / 4) * (conj eta ^ p * eta ^ q) = (-1 : ℂ) ^ (q % 4 + q / 4) := by
  have e1 : conj eta ^ p = conj eta ^ (p % 4) * (-1 : ℂ) ^ (p / 4) := by
    conv_lhs => rw [← Nat.mod_add_div p 4]
    rw [pow_add, pow_mul, conj_eta_pow_four]
  have e2 : eta ^ q = eta ^ (q % 4) * (-1 : ℂ) ^ (q / 4) := by
    conv_lhs => rw [← Nat.mod_add_div q 4]
    rw [pow_add, pow_mul, eta_pow_four]
  have hr : conj eta ^ (q % 4) * eta ^ (q % 4) = 1 := by
    rw [← mul_pow, mul_comm (conj eta) eta, eta_mul_conj_eta, one_pow]
  have hs : ∀ m n : ℕ, (-1 : ℂ) ^ (n + 2 * m) = (-1 : ℂ) ^ n := fun m n => by
    rw [pow_add, pow_mul]
    norm_num
  have hP : (-1 : ℂ) ^ (q % 4 + p / 4) * (-1 : ℂ) ^ (p / 4) * (-1 : ℂ) ^ (q / 4)
      = (-1 : ℂ) ^ (q % 4 + q / 4) := by
    rw [← pow_add, ← pow_add,
      show q % 4 + p / 4 + p / 4 + q / 4 = (q % 4 + q / 4) + 2 * (p / 4) by omega, hs]
  rw [e1, e2, h]
  linear_combination ((-1 : ℂ) ^ (q % 4 + p / 4) * (-1 : ℂ) ^ (p / 4) * (-1 : ℂ) ^ (q / 4)) * hr + hP

/-- Hermitian symmetry on monomials `X^p, X^q`. -/
theorem pairing_X_pow_herm (a : ℝ) (p q : ℕ) :
    pairing a (X ^ p) (X ^ q) = conj (pairing a (X ^ q) (X ^ p)) := by
  by_cases h : p % 4 = q % 4
  · rw [pairing_X_pow a p q, pairing_X_pow a q p, map_mul, map_pow, map_neg, map_one,
      conj_moment a p q]
    linear_combination (-(∫ z : ℂ, z ^ p * conj z ^ q * density a z)) * sign_herm p q h
  · rw [pairing_X_pow_eq_zero a p q h, pairing_X_pow_eq_zero a q p (fun h' => h h'.symm),
      map_zero]

/-- Hermitian symmetry of the pairing. -/
theorem pairing_herm (a : ℝ) (ha : 0 < a) (f g : ℂ[X]) :
    pairing a f g = conj (pairing a g f) := by
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 =>
    rw [pairing_add_left a ha, h1, h2, pairing_add_right a ha g f1 f2, map_add]
  | monomial p c =>
    induction g using Polynomial.induction_on' with
    | add g1 g2 h1 h2 =>
      rw [pairing_add_right a ha, h1, h2, pairing_add_left a ha g1 g2, map_add]
    | monomial q d =>
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
      simp only [pairing_C_mul_left, pairing_C_mul_right, map_mul, conj_conj]
      rw [← pairing_X_pow_herm a p q]
      ring

/-- Integration by parts in pairing form. -/
theorem pairing_ibp_of_moment (a : ℝ) (ha : 0 < a)
    (hmom : ∀ p q : ℕ, (p : ℂ) * (∫ z : ℂ, z ^ (p - 1) * conj z ^ q * density a z)
      + I * (∫ z : ℂ, z ^ (p + 3) * conj z ^ q * density a z)
      = (a : ℂ) * ∫ z : ℂ, z ^ p * conj z ^ (q + 1) * density a z)
    (f : ℂ[X]) (q : ℕ) :
    pairing a (derivative f + C I * X ^ 3 * f) (X ^ q) =
      -(tau q : ℂ) * a * pairing a f (X ^ (q + 1)) := by
  -- the sign relation `ε(q) = -τ(q) ε(q+1)`, with `ε(n) = (-1)^{n%4 + n/4}`
  have hsign : ∀ n : ℕ, (-1 : ℂ) ^ (n % 4 + n / 4)
      = -(tau n : ℂ) * (-1 : ℂ) ^ ((n + 1) % 4 + (n + 1) / 4) := by
    intro n
    rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h | h | h | h
    · have e : (n + 1) % 4 + (n + 1) / 4 = (n % 4 + n / 4) + 1 := by omega
      have ht : tau n = 1 := by unfold tau; rw [if_neg (show ¬ (n % 4 = 3) by omega)]
      rw [e, pow_succ, ht]
      push_cast
      ring
    · have e : (n + 1) % 4 + (n + 1) / 4 = (n % 4 + n / 4) + 1 := by omega
      have ht : tau n = 1 := by unfold tau; rw [if_neg (show ¬ (n % 4 = 3) by omega)]
      rw [e, pow_succ, ht]
      push_cast
      ring
    · have e : (n + 1) % 4 + (n + 1) / 4 = (n % 4 + n / 4) + 1 := by omega
      have ht : tau n = 1 := by unfold tau; rw [if_neg (show ¬ (n % 4 = 3) by omega)]
      rw [e, pow_succ, ht]
      push_cast
      ring
    · have e : n % 4 + n / 4 = ((n + 1) % 4 + (n + 1) / 4) + 2 := by omega
      have ht : tau n = -1 := by unfold tau; rw [if_pos h]
      rw [e, pow_add, ht]
      push_cast
      ring
  -- the monomial `X^n`
  have hX : ∀ n : ℕ, pairing a (derivative (X ^ n) + C I * X ^ 3 * X ^ n) (X ^ q)
      = -(tau q : ℂ) * a * pairing a (X ^ n) (X ^ (q + 1)) := by
    intro n
    have e1 : C I * X ^ 3 * X ^ n = C I * X ^ (n + 3) := by ring
    rw [derivative_X_pow, e1, pairing_add_left a ha]
    simp only [pairing_C_mul_left]
    rw [pairing_X_pow a (n - 1) q, pairing_X_pow a (n + 3) q, pairing_X_pow a n (q + 1)]
    linear_combination (-1 : ℂ) ^ (q % 4 + q / 4) * hmom n q
      + ((a : ℂ) * ∫ z : ℂ, z ^ n * conj z ^ (q + 1) * density a z) * hsign q
  induction f using Polynomial.induction_on' with
  | add f1 f2 h1 h2 =>
    have e : derivative (f1 + f2) + C I * X ^ 3 * (f1 + f2)
        = (derivative f1 + C I * X ^ 3 * f1) + (derivative f2 + C I * X ^ 3 * f2) := by
      rw [derivative_add]
      ring
    rw [e, pairing_add_left a ha (derivative f1 + C I * X ^ 3 * f1)
      (derivative f2 + C I * X ^ 3 * f2) (X ^ q), h1, h2, pairing_add_left a ha f1 f2 (X ^ (q + 1))]
    ring
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    have e : derivative (C c * X ^ n) + C I * X ^ 3 * (C c * X ^ n)
        = C c * (derivative (X ^ n) + C I * X ^ 3 * X ^ n) := by
      rw [derivative_C_mul]
      ring
    rw [e, pairing_C_mul_left, pairing_C_mul_left, hX n]
    ring

end Painleve
