import Painleve.BlockAlg
import Painleve.Weighted
import Painleve.PhiHankel
import Painleve.BiMoment
import Painleve.Kernel

open Complex Polynomial MeasureTheory Finset
open scoped ComplexConjugate ContDiff

namespace Painleve

/-- Positivity of the rising factorial at a positive point. -/
lemma ascPoch_pos (x : ℝ) (hx : 0 < x) (j : ℕ) : 0 < (ascPochhammer ℝ j).eval x := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_pos ih (by positivity)

/-- The weight of the bimoments. -/
noncomputable def bw (α β y s : ℝ) : ℝ :=
  Real.exp (-y * s) * s ^ (α - 1 / 2) * (1 + s ^ 2) ^ (-(β + 1 / 2))

/-- The ratio `ψ(s) = s²/(1+s²)`. -/
noncomputable def bpsi (s : ℝ) : ℝ := s ^ 2 / (1 + s ^ 2)

lemma bpsi_strictMono : StrictMonoOn bpsi (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  unfold bpsi
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos ha' hb']

lemma bpsi_nonneg (s : ℝ) : 0 ≤ bpsi s := by
  unfold bpsi
  positivity

lemma bpsi_le_one (s : ℝ) : bpsi s ≤ 1 := by
  unfold bpsi
  rw [div_le_one (by positivity)]
  linarith [sq_nonneg s]

lemma bw_pos (α β y s : ℝ) (hs : 0 < s) : 0 < bw α β y s := by
  unfold bw
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _))
    (Real.rpow_pos_of_pos (by positivity) _)

/-- Positivity of the bimoment Gram determinant. -/
theorem bimoment_det_pos (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) (k : ℕ) :
    0 < (Matrix.of fun p q : Fin k => Bmom α β y p q).det := by
  have hint : ∀ p q : Fin k, Integrable
      (fun s : ℝ => (s ^ (p : ℕ) * bw α β y s) * bpsi s ^ (q : ℕ))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro p q
    have hdom : IntegrableOn (fun s : ℝ => Real.exp (-y * s) * s ^ (α - 1 / 2) * s ^ (p : ℕ) *
        (1 + s ^ 2) ^ (-(β + 1 / 2))) (Set.Ioi 0) := by
      have h := kernel_pow_integrable α y 1 (p : ℕ) (-(β + 1 / 2)) hy one_pos hα
      simpa only [one_mul] using h
    refine Integrable.mono' hdom ?_ ?_
    · apply Measurable.aestronglyMeasurable
      unfold bw bpsi
      fun_prop
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
      have hs0 : 0 < s := hs
      have hpq : bpsi s ^ (q : ℕ) ≤ 1 := pow_le_one₀ (bpsi_nonneg s) (bpsi_le_one s)
      have hX : 0 ≤ s ^ (p : ℕ) * bw α β y s :=
        mul_nonneg (pow_nonneg hs0.le _) (bw_pos α β y s hs0).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hX (pow_nonneg (bpsi_nonneg s) _))]
      calc (s ^ (p : ℕ) * bw α β y s) * bpsi s ^ (q : ℕ)
          ≤ s ^ (p : ℕ) * bw α β y s := mul_le_of_le_one_right hX hpq
        _ = _ := by unfold bw; ring
  have key := det_bimoment_pos (bw α β y) bpsi (fun s hs => bw_pos α β y s hs)
    bpsi_strictMono hint
  have heq : (Matrix.of fun p q : Fin k => Bmom α β y p q) =
      Matrix.of fun p q : Fin k => ∫ s in Set.Ioi (0 : ℝ),
        (s ^ (p : ℕ) * bw α β y s) * bpsi s ^ (q : ℕ) := by
    ext p q
    simp only [Matrix.of_apply]
    unfold Bmom
    congr 1
    funext s
    unfold bw bpsi
    ring
  rw [heq]
  exact key


lemma Phi_comp_exp_contDiff (α β y : ℝ) (hα : 0 ≤ α) (hy : 0 < y) :
    ContDiff ℝ ∞ (fun t : ℝ => Phi α β y (Real.exp t)) :=
  (Phi_contDiffOn α β y hα hy).comp_contDiff Real.contDiff_exp (fun t => Real.exp_pos t)

lemma iter_ofReal_const_mul (A : ℝ) (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    iteratedDeriv n (fun t => ((A * G t : ℝ) : ℂ)) 0 = ((A * iteratedDeriv n G 0 : ℝ) : ℂ) := by
  have h1 := iteratedDeriv_ofReal_comm (fun t => A * G t) isOpen_univ
    (contDiff_const.mul hG).contDiffOn n 0 (Set.mem_univ 0)
  rw [h1]
  congr 1
  exact iteratedDeriv_const_mul_field A G

lemma det_const_mul' {k : ℕ} (A : ℝ) (X : Matrix (Fin k) (Fin k) ℝ) :
    (Matrix.of fun p q : Fin k => A * X p q).det = A ^ k * X.det := by
  have h : (Matrix.of fun p q : Fin k => A * X p q) = A • X := by
    ext p q
    simp [Matrix.smul_apply]
  rw [h, Matrix.det_smul, Fintype.card_fin]

lemma det_ofReal_mat {k : ℕ} (Y : Matrix (Fin k) (Fin k) ℝ) :
    (Matrix.of fun p q : Fin k => ((Y p q : ℝ) : ℂ)).det = ((Y.det : ℝ) : ℂ) := by
  have e : (Matrix.of fun p q : Fin k => ((Y p q : ℝ) : ℂ)) = Y.map Complex.ofRealHom := by
    ext p q
    simp
  rw [e, ← RingHom.mapMatrix_apply]
  exact (RingHom.map_det Complex.ofRealHom Y).symm

/-- Splitting a double sum over `Fin k` into a double sum over `range (p+1) × range (q+1)`. -/
lemma sum_fin_range {k : ℕ} (p q : ℕ) (hp : p < k) (hq : q < k) (F : ℕ → ℕ → ℂ)
    (hi : ∀ i j, p < i → F i j = 0) (hj : ∀ i j, q < j → F i j = 0) :
    ∑ i : Fin k, ∑ j : Fin k, F (i : ℕ) (j : ℕ) = ∑ i ∈ range (p + 1), ∑ j ∈ range (q + 1), F i j := by
  have hinner : ∀ i : ℕ, ∑ j : Fin k, F i (j : ℕ) = ∑ j ∈ range (q + 1), F i j := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => F i j) k]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro j _ hj'
    exact hj i j (by simp only [Finset.mem_range, not_lt] at hj'; omega)
  calc ∑ i : Fin k, ∑ j : Fin k, F (i : ℕ) (j : ℕ)
      = ∑ i : Fin k, ∑ j ∈ range (q + 1), F (i : ℕ) j :=
        Finset.sum_congr rfl fun i _ => hinner i
    _ = ∑ i ∈ range k, ∑ j ∈ range (q + 1), F i j :=
        Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range (q + 1), F i j) k
    _ = ∑ i ∈ range (p + 1), ∑ j ∈ range (q + 1), F i j := by
        refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_).symm
        intro i _ hi'
        refine Finset.sum_eq_zero fun j _ => hi i j (by simp only [Finset.mem_range, not_lt] at hi'; omega)

/-- The weight-space closed forms: `wsrc r` equals a constant times `Φ` at `e^t`. -/
lemma wsrc_form (a : ℝ) (ha : 0 < a) (r : ℕ) (hr : r < 4) :
    ∃ A α β : ℝ, 0 < A ∧ 0 ≤ α ∧ 0 ≤ β ∧
      ∀ t : ℝ, wsrc r a (Real.exp (t / 2)) = ((A * Phi α β (a ^ 2 / 2) (Real.exp t) : ℝ) : ℂ) := by
  have hsq : ∀ t : ℝ, Real.exp (t / 2) ^ 2 = Real.exp t := fun t => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpos : ∀ t : ℝ, 0 < Real.exp (t / 2) := fun t => Real.exp_pos _
  interval_cases r
  · refine ⟨Real.sqrt (Real.pi / 2), 0, 0, by positivity, le_rfl, le_rfl, fun t => ?_⟩
    rw [wsrc_zero a _ ha (hpos t), hsq t]
  · refine ⟨a * Real.sqrt (Real.pi / 2), 1, 0, by positivity, by norm_num, le_rfl, fun t => ?_⟩
    rw [wsrc_one a _ ha (hpos t), hsq t]
  · refine ⟨2 * Real.sqrt (Real.pi / 2), 1, 1, by positivity, by norm_num, by norm_num,
      fun t => ?_⟩
    rw [wsrc_two a _ ha (hpos t), hsq t]
  · refine ⟨2 * a * Real.sqrt (Real.pi / 2), 2, 1, by positivity, by norm_num, by norm_num,
      fun t => ?_⟩
    rw [wsrc_three a _ ha (hpos t), hsq t]


/-- **Sign of every Gram block determinant** (paper Proposition 4.4). -/
theorem det_blockGram_sign (a : ℝ) (ha : 0 < a) (r k : ℕ) (hr : r < 4)
    (hH : ∀ p q : ℕ,
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        (stirS p i : ℂ) * (stirS q j : ℂ) * (I / 4) ^ (i + j) * wmomE a r i j =
      iteratedDeriv (p + q) (fun t : ℝ => wsrc r a (Real.exp (t / 2))) 0) :
    ∃ c : ℝ, 0 < c ∧ (blockGram a r k).det = (((-1 : ℝ) ^ (r * k + k * (k - 1) / 2) * c : ℝ) : ℂ) := by
  obtain ⟨A, α, β, hA, hα, hβ, hform⟩ := wsrc_form a ha r hr
  have hy : 0 < a ^ 2 / 2 := by positivity
  have h1 := det_blockGram a r k hr
  have h2 := det_stirling_conj k (Matrix.of fun i j : Fin k => (I / 4) ^ ((i : ℕ) + j) * wmomE a r i j)
  have h3 : (Matrix.of fun p q : Fin k => ∑ i : Fin k, ∑ j : Fin k,
      (stirS p i : ℂ) * (stirS q j : ℂ) *
        (Matrix.of fun i j : Fin k => (I / 4) ^ ((i : ℕ) + j) * wmomE a r i j) i j)
      = Matrix.of fun p q : Fin k =>
          iteratedDeriv ((p : ℕ) + q) (fun t : ℝ => wsrc r a (Real.exp (t / 2))) 0 := by
    ext p q
    simp only [Matrix.of_apply]
    rw [← hH p q]
    have e := sum_fin_range (k := k) (p : ℕ) (q : ℕ) p.isLt q.isLt
      (fun i j => (stirS (p : ℕ) i : ℂ) * (stirS (q : ℕ) j : ℂ) * ((I / 4) ^ (i + j) * wmomE a r i j))
      (fun i j hi => by simp [stirS_eq_zero_of_lt hi])
      (fun i j hj => by simp [stirS_eq_zero_of_lt hj])
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl).trans (e.trans ?_)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hFfun : (fun t : ℝ => wsrc r a (Real.exp (t / 2)))
      = fun t => ((A * Phi α β (a ^ 2 / 2) (Real.exp t) : ℝ) : ℂ) := funext hform
  have hG := Phi_comp_exp_contDiff α β (a ^ 2 / 2) hα hy
  have h4 : (Matrix.of fun p q : Fin k =>
      iteratedDeriv ((p : ℕ) + q) (fun t : ℝ => wsrc r a (Real.exp (t / 2))) 0)
      = Matrix.of fun p q : Fin k => ((A * iteratedDeriv ((p : ℕ) + q)
          (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0 : ℝ) : ℂ) := by
    ext p q
    simp only [Matrix.of_apply]
    rw [hFfun, iter_ofReal_const_mul A _ hG]
  have hpos : 0 < 16 ^ (k * (k - 1) / 2) * (A ^ k * (((a ^ 2 / 2) / 2) ^ (k * (k - 1) / 2) *
      (∏ j : Fin k, (ascPochhammer ℝ j).eval (β + 1 / 2)) *
      (Matrix.of fun p q : Fin k => Bmom α β (a ^ 2 / 2) p q).det)) := by
    have hprod : 0 < ∏ j : Fin k, (ascPochhammer ℝ j).eval (β + 1 / 2) :=
      Finset.prod_pos fun j _ => ascPoch_pos _ (by linarith) j
    have hdet := bimoment_det_pos α β (a ^ 2 / 2) hα hy k
    positivity
  refine ⟨16 ^ (k * (k - 1) / 2) * (A ^ k * (((a ^ 2 / 2) / 2) ^ (k * (k - 1) / 2) *
      (∏ j : Fin k, (ascPochhammer ℝ j).eval (β + 1 / 2)) *
      (Matrix.of fun p q : Fin k => Bmom α β (a ^ 2 / 2) p q).det)), hpos, ?_⟩
  have h5 : (Matrix.of fun p q : Fin k => ((A * iteratedDeriv ((p : ℕ) + q)
      (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0 : ℝ) : ℂ)).det
      = (((Matrix.of fun p q : Fin k => A * iteratedDeriv ((p : ℕ) + q)
          (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0).det : ℝ) : ℂ) :=
    det_ofReal_mat (Matrix.of fun p q : Fin k => A * iteratedDeriv ((p : ℕ) + q)
      (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0)
  have h6 : (Matrix.of fun p q : Fin k => A * iteratedDeriv ((p : ℕ) + q)
      (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0).det
      = A ^ k * (Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q)
          (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0).det :=
    det_const_mul' A (Matrix.of fun p q : Fin k => iteratedDeriv ((p : ℕ) + q)
      (fun t => Phi α β (a ^ 2 / 2) (Real.exp t)) 0)
  rw [h1, ← h2, h3, h4, h5, h6, hankel_Phi_det α β (a ^ 2 / 2) hα hβ hy k]
  push_cast
  ring

end Painleve
