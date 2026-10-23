import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gauss's multiplication formula for positive real arguments

For an integer `d ≥ 1` and `s > 0`,
`Γ(s) = d^{s-1} ∏_{k<d} Γ((s+k)/d) / ∏_{k<d} Γ((1+k)/d)`
(DLMF 5.5.6, with the constant left unevaluated). The proof follows the
Bohr–Mollerup argument that Mathlib uses for the doubling formula
(`Real.doublingGamma_eq_Gamma`). The ratio form `Gamma_ratio_mult` is the
input to the Gamma representation (`prop:gamma`).
-/

open Real Set

namespace Painleve

/-- `d^{s-1} ∏_{k<d} Γ((s+k)/d) / ∏_{k<d} Γ((1+k)/d)`; equal to `Γ(s)` for `s > 0`. -/
noncomputable def multGamma (d : ℕ) (s : ℝ) : ℝ :=
  (d : ℝ) ^ (s - 1) * (∏ k ∈ Finset.range d, Gamma ((s + k) / d)) /
    ∏ k ∈ Finset.range d, Gamma ((1 + k) / d)

lemma prod_Gamma_shift (d : ℕ) (hd : 0 < d) (s : ℝ) (hs : s ≠ 0) :
    ∏ k ∈ Finset.range d, Gamma ((s + 1 + k) / d)
      = s / d * ∏ k ∈ Finset.range d, Gamma ((s + k) / d) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  set f : ℕ → ℝ := fun k => Gamma ((s + k) / ((m + 1 : ℕ) : ℝ)) with hf
  have hL : ∏ k ∈ Finset.range (m + 1), Gamma ((s + 1 + k) / ((m + 1 : ℕ) : ℝ))
      = ∏ k ∈ Finset.range (m + 1), f (k + 1) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hf]; push_cast; ring_nf
  have hlast : f (m + 1) = s / ((m + 1 : ℕ) : ℝ) * f 0 := by
    simp only [hf]
    have e : (s + ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) = s / ((m + 1 : ℕ) : ℝ) + 1 := by
      field_simp
    rw [e, Gamma_add_one (div_ne_zero hs hd')]
    simp
  show ∏ k ∈ Finset.range (m + 1), Gamma ((s + 1 + k) / ((m + 1 : ℕ) : ℝ))
      = s / ((m + 1 : ℕ) : ℝ) * ∏ k ∈ Finset.range (m + 1), f k
  rw [hL, Finset.prod_range_succ, Finset.prod_range_succ' f, hlast]
  ring

lemma multGamma_add_one (d : ℕ) (hd : 0 < d) (s : ℝ) (hs : s ≠ 0) :
    multGamma d (s + 1) = s * multGamma d s := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  unfold multGamma
  rw [show s + 1 - 1 = (s - 1) + 1 by ring, rpow_add hd', rpow_one, prod_Gamma_shift d hd s hs]
  field_simp

lemma multGamma_one (d : ℕ) (hd : 0 < d) : multGamma d 1 = 1 := by
  unfold multGamma
  rw [sub_self, rpow_zero, one_mul]
  refine div_self (Finset.prod_ne_zero_iff.mpr fun k _ => (Gamma_pos_of_pos ?_).ne')
  positivity

lemma multGamma_pos (d : ℕ) (hd : 0 < d) {s : ℝ} (hs : 0 < s) : 0 < multGamma d s := by
  unfold multGamma
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  refine div_pos (mul_pos (rpow_pos_of_pos hd' _) (Finset.prod_pos fun k _ => ?_))
    (Finset.prod_pos fun k _ => ?_) <;> exact Gamma_pos_of_pos (by positivity)

lemma convexOn_log_Gamma_affine (d : ℕ) (hd : 0 < d) (k : ℕ) :
    ConvexOn ℝ (Ioi 0) (fun s : ℝ => log (Gamma ((s + k) / d))) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let g : ℝ →ᵃ[ℝ] ℝ :=
    (DistribSMul.toLinearMap ℝ ℝ (1 / (d : ℝ))).toAffineMap + AffineMap.const ℝ ℝ ((k : ℝ) / d)
  have hg : ∀ s, g s = (s + k) / d := by
    intro s
    change (1 / (d : ℝ)) • s + (k : ℝ) / d = _
    rw [smul_eq_mul]; ring
  have h := convexOn_log_Gamma.comp_affineMap g
  refine (h.subset ?_ (convex_Ioi 0)).congr ?_
  · intro s hs
    simp only [mem_preimage, hg, mem_Ioi] at hs ⊢
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact div_pos (by linarith) hd'
  · intro s _
    simp only [Function.comp_apply, hg]

lemma convexOn_sum_log_Gamma (d : ℕ) (hd : 0 < d) (n : ℕ) :
    ConvexOn ℝ (Ioi 0) (fun s : ℝ => ∑ k ∈ Finset.range n, log (Gamma ((s + k) / d))) := by
  induction n with
  | zero => simpa using (convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ)))
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    exact ih.add (convexOn_log_Gamma_affine d hd n)

lemma multGamma_log_convex (d : ℕ) (hd : 0 < d) :
    ConvexOn ℝ (Ioi 0) (log ∘ multGamma d) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set C := ∏ k ∈ Finset.range d, Gamma ((1 + k) / d) with hC
  have hlin : ConvexOn ℝ (Ioi (0 : ℝ)) (fun s : ℝ => (s - 1) * log d) := by
    have := (convexOn_id (convex_Ioi (0 : ℝ))).smul (log_nonneg (by
      exact_mod_cast hd : (1 : ℝ) ≤ d))
    refine (this.add_const (-log d)).congr ?_
    intro s _; simp only [Pi.add_apply, smul_eq_mul, id]; ring
  refine ((convexOn_sum_log_Gamma d hd d).add hlin |>.add_const (-log C)).congr ?_
  intro s hs
  have hs' : 0 < s := hs
  have hP : ∀ k ∈ Finset.range d, Gamma ((s + k) / d) ≠ 0 :=
    fun k _ => (Gamma_pos_of_pos (by positivity)).ne'
  have hCne : C ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => (Gamma_pos_of_pos (by positivity)).ne'
  simp only [Function.comp_apply, multGamma]
  rw [← hC, log_div (mul_ne_zero (rpow_pos_of_pos hd' _).ne' (Finset.prod_ne_zero_iff.mpr hP))
      hCne, log_mul (rpow_pos_of_pos hd' _).ne' (Finset.prod_ne_zero_iff.mpr hP),
    log_rpow hd', log_prod hP]
  simp only [Pi.add_apply]
  ring

/-- Gauss's multiplication formula: `multGamma d s = Γ(s)` for `s > 0`. -/
theorem multGamma_eq_Gamma (d : ℕ) (hd : 0 < d) {s : ℝ} (hs : 0 < s) :
    multGamma d s = Gamma s :=
  eq_Gamma_of_log_convex (multGamma_log_convex d hd)
    (fun {y} hy => multGamma_add_one d hd y hy.ne') (fun {y} hy => multGamma_pos d hd hy)
    (multGamma_one d hd) hs

/-- Ratio form: for `x, y > 0`,
`Γ(x)/Γ(y) = d^{x-y} ∏_{k<d} Γ((x+k)/d)/Γ((y+k)/d)`. -/
theorem Gamma_ratio_mult (d : ℕ) (hd : 0 < d) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Gamma x / Gamma y
      = (d : ℝ) ^ (x - y) * ∏ k ∈ Finset.range d, (Gamma ((x + k) / d) / Gamma ((y + k) / d)) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [← multGamma_eq_Gamma d hd hx, ← multGamma_eq_Gamma d hd hy]
  unfold multGamma
  have hC : ∏ k ∈ Finset.range d, Gamma ((1 + k) / d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => (Gamma_pos_of_pos (by positivity)).ne'
  have hPy : ∏ k ∈ Finset.range d, Gamma ((y + k) / d) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => (Gamma_pos_of_pos (by positivity)).ne'
  have hxy : (d : ℝ) ^ (x - 1) = (d : ℝ) ^ (x - y) * (d : ℝ) ^ (y - 1) := by
    rw [← rpow_add hd']; congr 1; ring
  rw [Finset.prod_div_distrib, hxy]
  have := (rpow_pos_of_pos hd' (y - 1)).ne'
  field_simp

end Painleve
