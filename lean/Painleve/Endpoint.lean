import Painleve.EndpointProb
import Painleve.MainD
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The endpoint `a = 0` (Corollary 4.2 of `paper.tex`)

`S_r = G_{r,j_r} R_r`; conditioning on `R_r` and `E[e^{-sG}] = (1+s)^{-β}` give
`a^{-j_r} ∫|z|^{2r} ρ_a = π r! d^{-(d-2)β_r} E[(κ/(1+κR_r))^{β_r}]` with
`κ = d^{d-2} a^{-d}`; as `a → 0⁺`, `κ → ∞` and dominated convergence gives the
limit `π r! d^{-(d-2)β_r} E[R_r^{-β_r}]`.
-/

open MeasureTheory Set Filter Topology Complex Polynomial
open scoped MeasureTheory

namespace Painleve

variable {d : ℕ}

/-! ### The smallest shape comes first -/

lemma mem_shapeIdx (j r : ℕ) : j ∈ shapeIdx d r ↔ j < d ∧ j ≠ d - 1 - r := by
  simp [shapeIdx]

lemma shapeIdx_pairwise (r : ℕ) : (shapeIdx d r).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

lemma jMin_mem (hd : 2 ≤ d) (r : ℕ) (hr : r < d) : jMin d r ∈ shapeIdx d r := by
  rw [mem_shapeIdx]; unfold jMin; split_ifs <;> omega

lemma jMin_le (r : ℕ) (hr : r < d) (j : ℕ) (hj : j ∈ shapeIdx d r) : jMin d r ≤ j := by
  rw [mem_shapeIdx] at hj; unfold jMin; split_ifs <;> omega

lemma shapeIdx_head (hd : 2 ≤ d) (r : ℕ) (hr : r < d) :
    ∃ tl, shapeIdx d r = jMin d r :: tl ∧ tl.Nodup ∧ (∀ j ∈ tl, jMin d r < j) ∧
      (∀ j, j ∈ tl ↔ j < d ∧ j ≠ d - 1 - r ∧ j ≠ jMin d r) := by
  obtain ⟨h, tl, hl⟩ := List.exists_cons_of_ne_nil (shapeIdx_ne_nil hd r)
  have hpw := shapeIdx_pairwise (d := d) r
  rw [hl, List.pairwise_cons] at hpw
  have hh : h = jMin d r := by
    have h1 : jMin d r ≤ h := jMin_le r hr h (by rw [hl]; simp)
    have h2 : h ≤ jMin d r := by
      have hm := jMin_mem hd r hr
      rw [hl, List.mem_cons] at hm
      rcases hm with hm | hm
      · rw [hm]
      · exact (hpw.1 _ hm).le
    omega
  subst hh
  refine ⟨tl, hl, hpw.2.nodup, fun j hj => hpw.1 j hj, fun j => ?_⟩
  constructor
  · intro hj
    have hj' : j ∈ shapeIdx d r := by rw [hl]; exact List.mem_cons_of_mem _ hj
    rw [mem_shapeIdx] at hj'
    exact ⟨hj'.1, hj'.2, (hpw.1 j hj).ne'⟩
  · rintro ⟨h1, h2, h3⟩
    have hj' : j ∈ shapeIdx d r := (mem_shapeIdx j r).mpr ⟨h1, h2⟩
    rw [hl, List.mem_cons] at hj'
    exact hj'.resolve_left h3

/-! ### The moments through the smallest factor -/

lemma momentD_gamma (hd : 2 ≤ d) (r : ℕ) (hr : r < d) {a : ℝ} (ha : 0 < a) :
    momentD d a r = ((Real.pi * r.factorial / a ^ (r + 1) *
      ∫ y, Real.exp (-((d : ℝ) ^ (d - 2) / a ^ d) * Real.exp y)
        ∂(prodLaw (shapesD d r)) : ℝ) : ℂ) := by
  rw [momentD_eq_srcW, srcW_gamma d r hd hr ha 1]
  congr 3
  funext y
  ring_nf

/-- Conditioning on the other factors: `E[e^{-κ S}] = E[(1 + κ R)^{-β_r}]`. -/
lemma laplace_split {β : ℝ} (hβ : 0 < β) (rest : List ℝ) (hrest : ∀ b ∈ rest, 0 < b) {κ : ℝ}
    (hκ : 0 ≤ κ) :
    ∫ y, Real.exp (-κ * Real.exp y) ∂(prodLaw (β :: rest))
      = ∫ y, (1 + κ * Real.exp y) ^ (-β) ∂(prodLaw rest) := by
  haveI := isProbabilityMeasure_logGammaLaw' hβ
  haveI := isProbabilityMeasure_prodLaw rest hrest
  have hint : Integrable (fun z => Real.exp (-κ * Real.exp z)) (prodLaw rest ∗ logGammaLaw β) := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) (Real.exp_pos _).le
  rw [prodLaw, Measure.conv_comm, integral_conv hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  have hpt : ∀ x : ℝ, Real.exp (-κ * Real.exp (y + x)) = Real.exp (-(κ * Real.exp y) * Real.exp x) := by
    intro x; rw [Real.exp_add]; ring_nf
  simp_rw [hpt]
  exact laplace_logGamma hβ (mul_nonneg hκ (Real.exp_pos _).le)

/-- `(1 + κR)^{-β} = κ^{-β} (κ/(1+κR))^β`. -/
lemma rpow_split {β κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    (1 + κ * R) ^ (-β) = κ ^ (-β) * (κ / (1 + κ * R)) ^ β := by
  have h1 : 0 < 1 + κ * R := by positivity
  rw [Real.div_rpow hκ.le h1.le, Real.rpow_neg h1.le, Real.rpow_neg hκ.le]
  field_simp

/-- **Corollary 4.2**, scalar part: `a^{-j_r} ∫|z|^{2r}ρ_a → endpointConst d r`. -/
theorem endpoint_limit (hd : 2 ≤ d) (r : ℕ) (hr : r < d) :
    Tendsto (fun a : ℝ => ((a : ℂ) ^ jMin d r)⁻¹ * momentD d a r) (𝓝[>] 0)
      (𝓝 (endpointConst d r : ℂ)) := by
  have hd0 : 0 < d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨tl, hl, hnd, hgt, hmem⟩ := shapeIdx_head hd r hr
  set β := shapeD d r (jMin d r) with hβdef
  have hβ : 0 < β := shapeD_pos d r _ hd0
  set rest := tl.map (shapeD d r) with hrest
  have hshapes : shapesD d r = β :: rest := by rw [shapesD, hl]; rfl
  have hrestpos : ∀ b ∈ rest, 0 < b := by
    intro b hb; obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb; exact shapeD_pos d r j hd0
  have hrestgt : ∀ b ∈ rest, β < b := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    have := hgt j hj
    rw [hβdef]; unfold shapeD
    apply div_lt_div_of_pos_right _ hdpos
    have : (jMin d r : ℝ) < j := by exact_mod_cast this
    linarith
  haveI := isProbabilityMeasure_prodLaw rest hrestpos
  obtain ⟨hIntR, hER⟩ := moment_prodLaw β rest hrestpos hrestgt
  -- the constant
  have hconst : endpointConst d r = Real.pi * r.factorial * (d : ℝ) ^ (-((d : ℝ) - 2) * β) *
      ∫ y, Real.exp (-β * y) ∂(prodLaw rest) := by
    rw [hER, endpointConst, ← hβdef]
    congr 1
    rw [hrest, List.map_map]
    have hfin : ((Finset.range d).filter (fun j => j ≠ d - 1 - r ∧ j ≠ jMin d r)) = tl.toFinset := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, hmem j]
    rw [hfin, List.prod_toFinset _ hnd]
    rfl
  -- the scaled moment as an expectation over `rest`
  set κ : ℝ → ℝ := fun a => (d : ℝ) ^ (d - 2) / a ^ d with hκdef
  have hscaled : ∀ a : ℝ, 0 < a → ((a : ℂ) ^ jMin d r)⁻¹ * momentD d a r
      = ((Real.pi * r.factorial * (d : ℝ) ^ (-((d : ℝ) - 2) * β) *
          ∫ y, (κ a / (1 + κ a * Real.exp y)) ^ β ∂(prodLaw rest) : ℝ) : ℂ) := by
    intro a ha
    have hκ : 0 < κ a := by rw [hκdef]; positivity
    rw [momentD_gamma hd r hr ha, hshapes, laplace_split hβ rest hrestpos hκ.le]
    have hint : ∫ y, (1 + κ a * Real.exp y) ^ (-β) ∂(prodLaw rest)
        = κ a ^ (-β) * ∫ y, (κ a / (1 + κ a * Real.exp y)) ^ β ∂(prodLaw rest) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      exact rpow_split hκ (Real.exp_pos y)
    rw [hint]
    -- `a^{-j_r} a^{-r-1} κ^{-β} = d^{-(d-2)β}` since `d β = r + 1 + j_r`
    have hdβ : (d : ℝ) * β = r + 1 + jMin d r := by
      rw [hβdef]; unfold shapeD; field_simp
    have hlogκ : Real.log (κ a) = ((d : ℝ) - 2) * Real.log d - d * Real.log a := by
      rw [hκdef, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Nat.cast_sub (by omega)]
      push_cast; ring
    have e1 : κ a ^ (-β) = (d : ℝ) ^ (-((d : ℝ) - 2) * β) * a ^ (r + 1 + jMin d r) := by
      rw [Real.rpow_def_of_pos hκ, Real.rpow_def_of_pos hdpos, hlogκ, ← Real.rpow_natCast,
        Real.rpow_def_of_pos ha, ← Real.exp_add]
      congr 1
      push_cast
      rw [show ((r : ℝ) + 1 + (jMin d r : ℝ)) = (d : ℝ) * β by rw [hdβ]]
      ring
    have hpow : ((a ^ jMin d r)⁻¹ : ℝ) * (1 / a ^ (r + 1)) * κ a ^ (-β)
        = (d : ℝ) ^ (-((d : ℝ) - 2) * β) := by
      rw [e1, show a ^ (r + 1 + jMin d r) = a ^ jMin d r * a ^ (r + 1) by
        rw [← pow_add]; ring_nf]
      field_simp
    push_cast
    rw [← hpow]
    push_cast
    ring
  -- dominated convergence
  have hκtend : Tendsto κ (𝓝[>] 0) atTop := by
    rw [hκdef]
    have h1 : Tendsto (fun a : ℝ => (a⁻¹) ^ d) (𝓝[>] 0) atTop :=
      (tendsto_pow_atTop hd0.ne').comp tendsto_inv_nhdsGT_zero
    have := h1.const_mul_atTop (show (0 : ℝ) < (d : ℝ) ^ (d - 2) by positivity)
    refine this.congr fun a => ?_
    rw [inv_pow]; ring
  have hlim : Tendsto (fun a => ∫ y, (κ a / (1 + κ a * Real.exp y)) ^ β ∂(prodLaw rest))
      (𝓝[>] 0) (𝓝 (∫ y, Real.exp (-β * y) ∂(prodLaw rest))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => Real.exp (-β * y)) ?_ ?_
      hIntR ?_
    · filter_upwards [hκtend.eventually_gt_atTop 0] with a ha
      refine (Continuous.rpow_const ?_ (fun _ => Or.inr hβ.le)).aestronglyMeasurable
      refine continuous_const.div (by fun_prop) fun y => ?_
      have := Real.exp_pos y
      positivity
    · filter_upwards [hκtend.eventually_gt_atTop 0] with a ha
      refine Eventually.of_forall fun y => ?_
      have hR := Real.exp_pos y
      have hq : κ a / (1 + κ a * Real.exp y) ≤ (Real.exp y)⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (κ a / (1 + κ a * Real.exp y)) ^ β ≤ ((Real.exp y)⁻¹) ^ β :=
            Real.rpow_le_rpow (by positivity) hq hβ.le
        _ = Real.exp (-β * y) := by
            rw [← Real.exp_neg, ← Real.exp_mul]; ring_nf
    · refine Eventually.of_forall fun y => ?_
      have hR := Real.exp_pos y
      have h1 : Tendsto (fun a => κ a / (1 + κ a * Real.exp y)) (𝓝[>] 0) (𝓝 ((Real.exp y)⁻¹)) := by
        have hinv : Tendsto (fun a => (κ a)⁻¹) (𝓝[>] 0) (𝓝 0) := tendsto_inv_atTop_zero.comp hκtend
        have h2 : Tendsto (fun a => ((κ a)⁻¹ + Real.exp y)⁻¹) (𝓝[>] 0) (𝓝 ((0 + Real.exp y)⁻¹)) :=
          (hinv.add_const _).inv₀ (by rw [zero_add]; exact hR.ne')
        rw [zero_add] at h2
        refine h2.congr' ?_
        filter_upwards [hκtend.eventually_gt_atTop 0] with a ha
        field_simp
      have h3 := h1.rpow_const (p := β) (Or.inl (inv_pos.mpr hR).ne')
      have hval : ((Real.exp y)⁻¹) ^ β = Real.exp (-β * y) := by
        rw [← Real.exp_neg, ← Real.exp_mul]; ring_nf
      rw [← hval]
      exact h3
  have hfinal := (Complex.continuous_ofReal.tendsto _).comp (hlim.const_mul
    (Real.pi * r.factorial * (d : ℝ) ^ (-((d : ℝ) - 2) * β)))
  rw [hconst]
  refine hfinal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (hscaled a ha).symm

/-! ### The Gram matrices -/

lemma gramLeadD_diag (hd : 2 ≤ d) {a : ℝ} (n : ℕ) (hn : n ≤ d) (p q : Fin n) :
    gramLeadD d a n p q = if p = q then (-1 : ℂ) ^ (p : ℕ) * momentD d a p else 0 := by
  have hd0 : 0 < d := by omega
  unfold gramLeadD
  split_ifs with h
  · subst h
    exact pairingD_X_pow_self hd0 a p (by omega)
  · refine pairingD_X_pow_eq_zero hd0 a p q ?_
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact fun h' => h (Fin.ext h')

/-- The limits of the diagonal entries: `C_r` for `r ≤ d - 2`, `0` for `r = d - 1`. -/
noncomputable def endpointDiag (d : ℕ) (r : ℕ) : ℂ :=
  if r = d - 1 then 0 else (-1 : ℂ) ^ r * (endpointConst d r : ℂ)

lemma tendsto_entry (hd : 2 ≤ d) (r : ℕ) (hr : r < d) :
    Tendsto (fun a : ℝ => (-1 : ℂ) ^ r * momentD d a r) (𝓝[>] 0) (𝓝 (endpointDiag d r)) := by
  have h := endpoint_limit hd r hr
  unfold endpointDiag
  split_ifs with hlast
  · -- `momentD = a · (a^{-1} momentD) → 0 · C`
    have hj : jMin d r = 1 := by unfold jMin; rw [if_pos hlast]
    rw [hj] at h
    simp only [pow_one] at h
    have ha : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    have hprod := (ha.mul h).const_mul ((-1 : ℂ) ^ r)
    rw [zero_mul, mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
    field_simp
  · have hj : jMin d r = 0 := by unfold jMin; rw [if_neg hlast]
    rw [hj] at h
    simp only [pow_zero, inv_one, one_mul] at h
    exact h.const_mul _

theorem tendsto_gram (hd : 2 ≤ d) (n : ℕ) (hn : n ≤ d) :
    Tendsto (fun a : ℝ => gramLeadD d a n) (𝓝[>] 0)
      (𝓝 (Matrix.diagonal fun p : Fin n => endpointDiag d p)) := by
  refine tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => ?_
  simp only [Matrix.diagonal_apply]
  have heq : ∀ a : ℝ, gramLeadD d a n p q
      = if p = q then (-1 : ℂ) ^ (p : ℕ) * momentD d a p else 0 :=
    fun a => gramLeadD_diag hd n hn p q
  simp_rw [heq]
  split_ifs with h
  · exact tendsto_entry hd p (by omega)
  · exact tendsto_const_nhds

lemma endpointConst_pos (hd : 2 ≤ d) (r : ℕ) (hr : r < d) : 0 < endpointConst d r := by
  have hd0 : 0 < d := by omega
  unfold endpointConst
  refine mul_pos (mul_pos (mul_pos Real.pi_pos (by exact_mod_cast Nat.factorial_pos r))
    (Real.rpow_pos_of_pos (by exact_mod_cast hd0) _)) (Finset.prod_pos fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  refine div_pos (Real.Gamma_pos_of_pos ?_) (Real.Gamma_pos_of_pos (shapeD_pos d r j hd0))
  have hlt : jMin d r < j := lt_of_le_of_ne (jMin_le r hr j ((mem_shapeIdx j r).mpr
    ⟨hj.1, hj.2.1⟩)) (Ne.symm hj.2.2)
  unfold shapeD
  rw [← sub_div]
  apply div_pos _ (by exact_mod_cast hd0)
  have : (jMin d r : ℝ) < j := by exact_mod_cast hlt
  linarith

/-- **Corollary 4.2** (`cor:endpoint`). -/
theorem endpoint_theorem : Stmt_endpoint := by
  intro d hd
  refine ⟨fun r hr => ⟨endpointConst_pos hd r hr, endpoint_limit hd r hr⟩, fun n hn => ?_, ?_⟩
  · refine ⟨Matrix.diagonal fun p : Fin n => endpointDiag d p, tendsto_gram hd n hn.le,
      fun i j hij => Matrix.diagonal_apply_ne _ hij, ?_⟩
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun p _ => ?_
    unfold endpointDiag
    rw [if_neg (by omega)]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Complex.ofReal_ne_zero.mpr (endpointConst_pos hd p (by omega)).ne')
  · refine ⟨Matrix.diagonal fun p : Fin d => endpointDiag d p, tendsto_gram hd d le_rfl,
      fun i j hij => Matrix.diagonal_apply_ne _ hij, ?_⟩
    rw [Matrix.rank_diagonal]
    have hcard : Fintype.card {p : Fin d // endpointDiag d p ≠ 0}
        = Fintype.card {p : Fin d // (p : ℕ) ≠ d - 1} := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun p => ?_)
      unfold endpointDiag
      split_ifs with h
      · simp [h]
      · simp only [ne_eq, h, not_false_eq_true, iff_true]
        exact mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Complex.ofReal_ne_zero.mpr (endpointConst_pos hd p p.isLt).ne')
    rw [hcard, Fintype.card_subtype_compl, Fintype.card_fin]
    have : Fintype.card {p : Fin d // (p : ℕ) = d - 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨⟨d - 1, by omega⟩, rfl⟩, fun ⟨p, hp⟩ => ?_⟩
      exact Subtype.ext (Fin.ext hp)
    rw [this]

end Painleve
