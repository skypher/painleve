import Painleve.Statement
open Complex Polynomial
open scoped ComplexConjugate
namespace Painleve

theorem eta_pow_four : eta ^ 4 = -1 := by
  unfold eta
  rw [← Complex.exp_nat_mul]
  have h : ((4 : ℕ) : ℂ) * (↑Real.pi * I / 4) = ↑Real.pi * I := by
    push_cast; ring
  rw [h, Complex.exp_pi_mul_I]

theorem eta_pow_eight : eta ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, eta_pow_four]
  norm_num

theorem eta_ne_zero : eta ≠ 0 := by
  intro h
  have h4 := eta_pow_four
  rw [h] at h4
  norm_num at h4

/-- The core identity: `(-η)^{-r} η^{r+4q} = (-1)^{r+q}`. -/
theorem twist_key (r q : ℕ) :
    (-eta) ^ (-((r : ℕ) : ℤ)) * eta ^ (r + 4 * q) = (-1 : ℂ) ^ (r + q) := by
  have hne : eta ≠ 0 := eta_ne_zero
  have h4 := eta_pow_four
  have hs : ((-1 : ℂ) ^ r) * ((-1 : ℂ) ^ r) = 1 := by
    rw [← mul_pow]; norm_num
  have hinv : ((-1 : ℂ) ^ r)⁻¹ = (-1 : ℂ) ^ r := inv_eq_of_mul_eq_one_right hs
  have he : eta ^ r ≠ 0 := pow_ne_zero _ hne
  have hneg : (-eta) ^ (-((r : ℕ) : ℤ)) = ((-1 : ℂ) ^ r * eta ^ r)⁻¹ := by
    rw [zpow_neg, zpow_natCast, neg_pow]
  rw [hneg, pow_add, pow_mul, h4, mul_inv, hinv, pow_add]
  field_simp

theorem twist_monomial (n : ℕ) (a : ℂ) :
    twist (monomial n a) = monomial n (a * ((-eta) ^ (-((n % 4 : ℕ) : ℤ)) * eta ^ n)) := by
  unfold twist
  rw [sum_monomial_index]
  · congr 1
    ring
  · simp

theorem twist_add (f g : ℂ[X]) : twist (f + g) = twist f + twist g := by
  unfold twist
  apply sum_add_index
  · intro i
    simp
  · intro a b₁ b₂
    simp [add_mul]

theorem twist_X_pow (m : ℕ) : twist (X ^ m) = C ((-1 : ℂ) ^ (m % 4 + m / 4)) * X ^ m := by
  simp only [X_pow_eq_monomial]
  rw [twist_monomial, C_mul_monomial]
  congr 1
  have h := twist_key (m % 4) (m / 4)
  rw [Nat.mod_add_div] at h
  rw [one_mul, mul_one, h]

theorem twist_C_mul (c : ℂ) (f : ℂ[X]) : twist (C c * f) = C c * twist f := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, twist_add, twist_add, hp, hq, mul_add]
  | monomial n a =>
    simp only [C_mul_monomial, twist_monomial, mul_assoc]

theorem tau_mul_self (l : ℕ) : tau l * tau l = 1 := by
  unfold tau
  split_ifs <;> norm_num

theorem tau_four (n : ℕ) :
    tau n * tau (n + 1) * tau (n + 2) * tau (n + 3) = -1 := by
  unfold tau
  split_ifs <;> first | omega | norm_num

theorem prod_range_add_four (n : ℕ) :
    ∏ l ∈ Finset.range (n + 4), tau l = -∏ l ∈ Finset.range n, tau l := by
  have h := tau_four n
  have e : ∏ l ∈ Finset.range (n + 4), tau l
      = (∏ l ∈ Finset.range n, tau l) * (tau n * tau (n + 1) * tau (n + 2) * tau (n + 3)) := by
    simp only [Finset.prod_range_succ]
    ring
  rw [e, h]
  ring

theorem prod_range_add_four_mul (q r : ℕ) (hr : r < 4) :
    ∏ l ∈ Finset.range (r + 4 * q), tau l = (-1 : ℝ) ^ q := by
  induction q with
  | zero =>
    interval_cases r <;> simp [Finset.prod_range_succ, tau]
  | succ q ih =>
    rw [show r + 4 * (q + 1) = (r + 4 * q) + 4 by ring, prod_range_add_four, ih, pow_succ]
    ring

theorem rhoSign_eq (n : ℕ) : rhoSign n = (-1) ^ (n + n / 4) := by
  have h := prod_range_add_four_mul (n / 4) (n % 4) (Nat.mod_lt _ (by norm_num))
  rw [Nat.mod_add_div] at h
  unfold rhoSign
  rw [h, pow_add]

theorem rhoSign_succ (n : ℕ) : rhoSign (n + 1) = - tau n * rhoSign n := by
  unfold rhoSign
  rw [Finset.prod_range_succ]
  ring

theorem rhoSign_add_three (n : ℕ) : rhoSign (n + 3) = tau (n + 3) * rhoSign n := by
  unfold rhoSign
  have h4 := tau_four n
  have h3 := tau_mul_self (n + 3)
  simp only [Finset.prod_range_succ]
  linear_combination
    (-((-1 : ℝ) ^ n * (∏ l ∈ Finset.range n, tau l) * tau (n + 3))) * h4
      + ((-1 : ℝ) ^ n * (∏ l ∈ Finset.range n, tau l) * (tau n * tau (n + 1) * tau (n + 2))) * h3

end Painleve
