import Painleve.UniqD3

/-!
# The localized energy identity (Section 8 of `paper.tex`)

For sequences with `a_n δ_n + ∑_{m=n-d+2}^{n} b_m D_m = -r_n`
(`D_m = ∑_{i=m}^{m+d-2} δ_i`, `eq:linearized`) and finitely supported `h`,
multiplying by `h_n² δ_n`, regrouping by windows and using
`(∑ z_i)(∑ h_i² z_i) = (∑ h_i z_i)² + ½ ∑_{i,j} (h_i - h_j)² z_i z_j`
(`eq:square-identity`, symmetric form) gives `eq:localized`.
-/

open Finset

namespace Painleve

/-- `eq:square-identity`, symmetric form. -/
theorem square_identity (L : ℕ) (z h : ℕ → ℝ) :
    (∑ i ∈ range L, z i) * (∑ i ∈ range L, h i ^ 2 * z i)
      = (∑ i ∈ range L, h i * z i) ^ 2 +
        (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, (h i - h j) ^ 2 * (z i * z j) := by
  have e1 : (∑ i ∈ range L, z i) * (∑ i ∈ range L, h i ^ 2 * z i)
      = ∑ i ∈ range L, ∑ j ∈ range L, z i * (h j ^ 2 * z j) := by rw [sum_mul_sum]
  have e1' : ∑ i ∈ range L, ∑ j ∈ range L, z i * (h j ^ 2 * z j)
      = ∑ i ∈ range L, ∑ j ∈ range L, z j * (h i ^ 2 * z i) := sum_comm
  have e2 : (∑ i ∈ range L, h i * z i) ^ 2
      = ∑ i ∈ range L, ∑ j ∈ range L, (h i * z i) * (h j * z j) := by rw [sq, sum_mul_sum]
  have key : (∑ i ∈ range L, z i) * (∑ i ∈ range L, h i ^ 2 * z i)
      = (1 / 2) * (∑ i ∈ range L, ∑ j ∈ range L, z i * (h j ^ 2 * z j) +
          ∑ i ∈ range L, ∑ j ∈ range L, z j * (h i ^ 2 * z i)) := by
    rw [← e1', e1]; ring
  rw [key, e2, ← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- Regrouping a sum over windows: `∑_n ∑_{j ≤ n} G(n-j, j) = ∑_m ∑_j G(m, j)`. -/
theorem window_regroup (L N : ℕ) (G : ℕ → ℕ → ℝ) (hG : ∀ m j, N ≤ m + j → G m j = 0) :
    ∑ n ∈ range N, ∑ j ∈ range L, (if j ≤ n then G (n - j) j else 0)
      = ∑ m ∈ range N, ∑ j ∈ range L, G m j := by
  rw [sum_comm, sum_comm (s := range N)]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_filter]
  have hfil : (range N).filter (fun n => j ≤ n) = Ico j N := by
    ext n; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hfil]
  by_cases hjN : j ≤ N
  · rw [sum_Ico_eq_sum_range]
    simp only [add_tsub_cancel_left]
    rw [← sum_range_add_sum_Ico _ (show N - j ≤ N by omega)]
    rw [sum_eq_zero (s := Ico (N - j) N) fun m hm => hG m j (by
      have := (mem_Ico.mp hm).1; omega), add_zero]
  · rw [Ico_eq_empty (by omega), sum_empty]
    exact (sum_eq_zero fun m hm => hG m j (by have := mem_range.mp hm; omega)).symm

/-- **The localized energy identity** (`eq:localized`). -/
theorem energy_identity (L N : ℕ) (a b δ r h : ℕ → ℝ) (hh : ∀ n, N ≤ n → h n = 0)
    (hlin : ∀ n, a n * δ n + ∑ j ∈ range L,
      (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0) = -r n) :
    ∑ n ∈ range N, a n * h n ^ 2 * δ n ^ 2 +
        ∑ m ∈ range N, b m * (∑ i ∈ range L, h (m + i) * δ (m + i)) ^ 2
      = -∑ n ∈ range N, r n * h n ^ 2 * δ n -
          ∑ m ∈ range N, b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
            (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j))) := by
  -- multiply the linearized equation by `h_n² δ_n` and sum
  have hsum : ∑ n ∈ range N, h n ^ 2 * δ n * (a n * δ n + ∑ j ∈ range L,
      (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0))
      = -∑ n ∈ range N, r n * h n ^ 2 * δ n := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [hlin n]; ring
  -- regroup the window terms
  have hreg : ∑ n ∈ range N, h n ^ 2 * δ n * ∑ j ∈ range L,
      (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0)
      = ∑ m ∈ range N, b m * ((∑ i ∈ range L, δ (m + i)) *
          (∑ j ∈ range L, h (m + j) ^ 2 * δ (m + j))) := by
    set G : ℕ → ℕ → ℝ := fun m j => b m * (∑ i ∈ range L, δ (m + i)) *
      (h (m + j) ^ 2 * δ (m + j)) with hGdef
    have h1 : ∀ n, h n ^ 2 * δ n * ∑ j ∈ range L,
        (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0)
        = ∑ j ∈ range L, (if j ≤ n then G (n - j) j else 0) := by
      intro n
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      split_ifs with hjn
      · rw [hGdef]; simp only; rw [show n - j + j = n by omega]; ring
      · ring
    rw [sum_congr rfl fun n _ => h1 n]
    rw [window_regroup L N G (fun m j hmj => by rw [hGdef]; simp only; rw [hh (m + j) hmj]; ring)]
    refine sum_congr rfl fun m _ => ?_
    rw [hGdef, mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hsplit : ∑ n ∈ range N, h n ^ 2 * δ n * (a n * δ n + ∑ j ∈ range L,
      (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0))
      = ∑ n ∈ range N, a n * h n ^ 2 * δ n ^ 2 + ∑ n ∈ range N, h n ^ 2 * δ n * ∑ j ∈ range L,
        (if j ≤ n then b (n - j) * ∑ i ∈ range L, δ (n - j + i) else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  rw [hsplit, hreg] at hsum
  have hsq : ∀ m, b m * ((∑ i ∈ range L, δ (m + i)) * (∑ j ∈ range L, h (m + j) ^ 2 * δ (m + j)))
      = b m * (∑ i ∈ range L, h (m + i) * δ (m + i)) ^ 2 +
        b m * ((1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
          (h (m + i) - h (m + j)) ^ 2 * (δ (m + i) * δ (m + j))) := by
    intro m
    rw [square_identity L (fun i => δ (m + i)) (fun i => h (m + i))]
    ring
  simp_rw [hsq] at hsum
  rw [sum_add_distrib] at hsum
  linarith

end Painleve
