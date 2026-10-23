import Painleve.BesselSeries

open scoped ContDiff

namespace Painleve

noncomputable def hSeries (a : ℝ) : ℝ :=
  Real.pi ^ 2 / 4 *
    (Real.sqrt 8 * besselS (-1 / 4) (a ^ 2 / 4) ^ 2
      - Real.sqrt 2 * a * besselS (-1 / 4) (a ^ 2 / 4) * besselS (1 / 4) (a ^ 2 / 4)
      + a ^ 2 / Real.sqrt 8 * besselS (1 / 4) (a ^ 2 / 4) ^ 2)

/-- `Uf n x = S^{(n)}(x²/4)` for `S = besselS (-1/4)`. -/
noncomputable def Uf (n : ℕ) (x : ℝ) : ℝ := iteratedDeriv n (besselS (-1 / 4)) (x ^ 2 / 4)

/-- `Vf n x = T^{(n)}(x²/4)` for `T = besselS (1/4)`. -/
noncomputable def Vf (n : ℕ) (x : ℝ) : ℝ := iteratedDeriv n (besselS (1 / 4)) (x ^ 2 / 4)

noncomputable def Kf (x : ℝ) : ℝ := (((Real.sqrt 8 * (Uf 0 x * Uf 0 x)) + (((1 / Real.sqrt 8) * (x * x)) * (Vf 0 x * Vf 0 x))) + ((((-Real.sqrt 2) * x) * Uf 0 x) * Vf 0 x))

noncomputable def E1f (x : ℝ) : ℝ := ((((((((-Real.sqrt 2) * Uf 0 x) * Vf 0 x) + (((((2 : ℝ)) * (1 / Real.sqrt 8)) * x) * (Vf 0 x * Vf 0 x))) + (((Real.sqrt 8 * x) * Uf 0 x) * Uf 1 x)) + ((((1 / Real.sqrt 8) * Vf 0 x) * Vf 1 x) * ((x * x) * x))) + ((((((1 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 0 x) * Vf 1 x) * (x * x))) + ((((((1 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 1 x) * Vf 0 x) * (x * x)))

noncomputable def E2f (x : ℝ) : ℝ := (((((((((((((((2 : ℝ)) * (1 / Real.sqrt 8)) * (Vf 0 x * Vf 0 x)) + ((Real.sqrt 8 * Uf 0 x) * Uf 1 x)) + (((((1 : ℝ) / 2) * Real.sqrt 8) * (x * x)) * (Uf 1 x * Uf 1 x))) + (((((1 : ℝ) / 2) * (1 / Real.sqrt 8)) * (((x * x) * x) * x)) * (Vf 1 x * Vf 1 x))) + ((((((1 : ℝ) / 2) * Real.sqrt 8) * Uf 0 x) * Uf 2 x) * (x * x))) + ((((((1 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 1 x) * Vf 1 x) * ((x * x) * x))) + ((((((1 : ℝ) / 2) * (1 / Real.sqrt 8)) * Vf 0 x) * Vf 2 x) * (((x * x) * x) * x))) + ((((((5 : ℝ)) * (1 / Real.sqrt 8)) * Vf 0 x) * Vf 1 x) * (x * x))) + ((((((1 : ℝ) / 4) * (-Real.sqrt 2)) * Uf 0 x) * Vf 2 x) * ((x * x) * x))) + ((((((1 : ℝ) / 4) * (-Real.sqrt 2)) * Uf 2 x) * Vf 0 x) * ((x * x) * x))) + ((((((3 : ℝ) / 2) * (-Real.sqrt 2)) * x) * Uf 0 x) * Vf 1 x)) + ((((((3 : ℝ) / 2) * (-Real.sqrt 2)) * x) * Uf 1 x) * Vf 0 x))

noncomputable def E3f (x : ℝ) : ℝ := ((((((((((((((((((((((3 : ℝ) / 2) * Real.sqrt 8) * x) * (Uf 1 x * Uf 1 x)) + (((((3 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 0 x) * Vf 1 x)) + (((((3 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 1 x) * Vf 0 x)) + (((((9 : ℝ) / 2) * (1 / Real.sqrt 8)) * ((x * x) * x)) * (Vf 1 x * Vf 1 x))) + ((((((3 : ℝ)) * (-Real.sqrt 2)) * Uf 1 x) * Vf 1 x) * (x * x))) + ((((((12 : ℝ)) * (1 / Real.sqrt 8)) * x) * Vf 0 x) * Vf 1 x)) + ((((((1 : ℝ) / 4) * Real.sqrt 8) * Uf 0 x) * Uf 3 x) * ((x * x) * x))) + ((((((1 : ℝ) / 4) * (1 / Real.sqrt 8)) * Vf 0 x) * Vf 3 x) * ((((x * x) * x) * x) * x))) + ((((((1 : ℝ) / 8) * (-Real.sqrt 2)) * Uf 0 x) * Vf 3 x) * (((x * x) * x) * x))) + ((((((1 : ℝ) / 8) * (-Real.sqrt 2)) * Uf 3 x) * Vf 0 x) * (((x * x) * x) * x))) + ((((((3 : ℝ) / 2) * Real.sqrt 8) * x) * Uf 0 x) * Uf 2 x)) + ((((((3 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 0 x) * Vf 2 x) * (x * x))) + ((((((3 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 2 x) * Vf 0 x) * (x * x))) + ((((((3 : ℝ) / 4) * Real.sqrt 8) * Uf 1 x) * Uf 2 x) * ((x * x) * x))) + ((((((3 : ℝ) / 4) * (1 / Real.sqrt 8)) * Vf 1 x) * Vf 2 x) * ((((x * x) * x) * x) * x))) + ((((((3 : ℝ) / 8) * (-Real.sqrt 2)) * Uf 1 x) * Vf 2 x) * (((x * x) * x) * x))) + ((((((3 : ℝ) / 8) * (-Real.sqrt 2)) * Uf 2 x) * Vf 1 x) * (((x * x) * x) * x))) + ((((((9 : ℝ) / 2) * (1 / Real.sqrt 8)) * Vf 0 x) * Vf 2 x) * ((x * x) * x)))

theorem hid (t : ℝ) : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id' t

theorem hcon (c t : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 t := hasDerivAt_const t c

theorem hasDerivAt_iter (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
  rw [iteratedDeriv_succ]
  exact ((hf.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n)) x).hasDerivAt

theorem hUfGen (n : ℕ) (t : ℝ) : HasDerivAt (Uf n) ((t / 2) * Uf (n + 1) t) t := by
  have hS : ContDiff ℝ ∞ (besselS (-1 / 4)) := besselS_contDiff _ (by norm_num)
  have h1 := hasDerivAt_iter (besselS (-1 / 4)) hS n (t ^ 2 / 4)
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (t / 2) t := by
    have this := (hasDerivAt_pow 2 t).div_const 4
    exact this.congr_deriv (by norm_num <;> ring)
  have h3 := h1.comp t h2
  refine h3.congr_deriv ?_
  unfold Uf
  ring

theorem hVfGen (n : ℕ) (t : ℝ) : HasDerivAt (Vf n) ((t / 2) * Vf (n + 1) t) t := by
  have hT : ContDiff ℝ ∞ (besselS (1 / 4)) := besselS_contDiff _ (by norm_num)
  have h1 := hasDerivAt_iter (besselS (1 / 4)) hT n (t ^ 2 / 4)
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (t / 2) t := by
    have this := (hasDerivAt_pow 2 t).div_const 4
    exact this.congr_deriv (by norm_num <;> ring)
  have h3 := h1.comp t h2
  refine h3.congr_deriv ?_
  unfold Vf
  ring

theorem hU0 (t : ℝ) : HasDerivAt (Uf 0) ((t / 2) * Uf 1 t) t := hUfGen 0 t
theorem hU1 (t : ℝ) : HasDerivAt (Uf 1) ((t / 2) * Uf 2 t) t := hUfGen 1 t
theorem hU2 (t : ℝ) : HasDerivAt (Uf 2) ((t / 2) * Uf 3 t) t := hUfGen 2 t
theorem hV0 (t : ℝ) : HasDerivAt (Vf 0) ((t / 2) * Vf 1 t) t := hVfGen 0 t
theorem hV1 (t : ℝ) : HasDerivAt (Vf 1) ((t / 2) * Vf 2 t) t := hVfGen 1 t
theorem hV2 (t : ℝ) : HasDerivAt (Vf 2) ((t / 2) * Vf 3 t) t := hVfGen 2 t

theorem hK_d (t : ℝ) : HasDerivAt Kf (E1f t) t := by
  refine ((((hcon (Real.sqrt 8) t).mul ((hU0 t).mul (hU0 t))).add (((hcon ((1 / Real.sqrt 8)) t).mul ((hid t).mul (hid t))).mul ((hV0 t).mul (hV0 t)))).add ((((hcon ((-Real.sqrt 2)) t).mul (hid t)).mul (hU0 t)).mul (hV0 t))).congr_deriv ?_
  unfold E1f
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

theorem hE1_d (t : ℝ) : HasDerivAt E1f (E2f t) t := by
  refine ((((((((hcon ((-Real.sqrt 2)) t).mul (hU0 t)).mul (hV0 t)).add ((((hcon (((2 : ℝ))) t).mul (hcon ((1 / Real.sqrt 8)) t)).mul (hid t)).mul ((hV0 t).mul (hV0 t)))).add ((((hcon (Real.sqrt 8) t).mul (hid t)).mul (hU0 t)).mul (hU1 t))).add ((((hcon ((1 / Real.sqrt 8)) t).mul (hV0 t)).mul (hV1 t)).mul (((hid t).mul (hid t)).mul (hid t)))).add (((((hcon (((1 : ℝ) / 2)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hU0 t)).mul (hV1 t)).mul ((hid t).mul (hid t)))).add (((((hcon (((1 : ℝ) / 2)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hU1 t)).mul (hV0 t)).mul ((hid t).mul (hid t)))).congr_deriv ?_
  unfold E2f
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

theorem hE2_d (t : ℝ) : HasDerivAt E2f (E3f t) t := by
  refine ((((((((((((((hcon (((2 : ℝ))) t).mul (hcon ((1 / Real.sqrt 8)) t)).mul ((hV0 t).mul (hV0 t))).add (((hcon (Real.sqrt 8) t).mul (hU0 t)).mul (hU1 t))).add ((((hcon (((1 : ℝ) / 2)) t).mul (hcon (Real.sqrt 8) t)).mul ((hid t).mul (hid t))).mul ((hU1 t).mul (hU1 t)))).add ((((hcon (((1 : ℝ) / 2)) t).mul (hcon ((1 / Real.sqrt 8)) t)).mul ((((hid t).mul (hid t)).mul (hid t)).mul (hid t))).mul ((hV1 t).mul (hV1 t)))).add (((((hcon (((1 : ℝ) / 2)) t).mul (hcon (Real.sqrt 8) t)).mul (hU0 t)).mul (hU2 t)).mul ((hid t).mul (hid t)))).add (((((hcon (((1 : ℝ) / 2)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hU1 t)).mul (hV1 t)).mul (((hid t).mul (hid t)).mul (hid t)))).add (((((hcon (((1 : ℝ) / 2)) t).mul (hcon ((1 / Real.sqrt 8)) t)).mul (hV0 t)).mul (hV2 t)).mul ((((hid t).mul (hid t)).mul (hid t)).mul (hid t)))).add (((((hcon (((5 : ℝ))) t).mul (hcon ((1 / Real.sqrt 8)) t)).mul (hV0 t)).mul (hV1 t)).mul ((hid t).mul (hid t)))).add (((((hcon (((1 : ℝ) / 4)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hU0 t)).mul (hV2 t)).mul (((hid t).mul (hid t)).mul (hid t)))).add (((((hcon (((1 : ℝ) / 4)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hU2 t)).mul (hV0 t)).mul (((hid t).mul (hid t)).mul (hid t)))).add (((((hcon (((3 : ℝ) / 2)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hid t)).mul (hU0 t)).mul (hV1 t))).add (((((hcon (((3 : ℝ) / 2)) t).mul (hcon ((-Real.sqrt 2)) t)).mul (hid t)).mul (hU1 t)).mul (hV0 t))).congr_deriv ?_
  unfold E3f
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring


theorem oS (x : ℝ) : x * iteratedDeriv 2 (besselS (-1 / 4)) x
    + (1 / 2) * iteratedDeriv 1 (besselS (-1 / 4)) x + x * iteratedDeriv 0 (besselS (-1 / 4)) x = 0 := by
  have h := besselS_ode (-1 / 4) (by norm_num) x
  rw [iteratedDeriv_one, iteratedDeriv_zero]
  linear_combination h

theorem oT (x : ℝ) : x * iteratedDeriv 2 (besselS (1 / 4)) x
    + (3 / 2) * iteratedDeriv 1 (besselS (1 / 4)) x + x * iteratedDeriv 0 (besselS (1 / 4)) x = 0 := by
  have h := besselS_ode (1 / 4) (by norm_num) x
  rw [iteratedDeriv_one, iteratedDeriv_zero]
  linear_combination h

theorem ode_deriv_gen (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (h : ∀ x, x * iteratedDeriv 2 f x + c * iteratedDeriv 1 f x + x * iteratedDeriv 0 f x = 0)
    (x : ℝ) :
    x * iteratedDeriv 3 f x + (c + 1) * iteratedDeriv 2 f x + iteratedDeriv 0 f x
      + x * iteratedDeriv 1 f x = 0 := by
  have hg : (fun y : ℝ => y * iteratedDeriv 2 f y + c * iteratedDeriv 1 f y
      + y * iteratedDeriv 0 f y) = fun _ => 0 := funext h
  have h0 : HasDerivAt (fun y : ℝ => y * iteratedDeriv 2 f y + c * iteratedDeriv 1 f y
      + y * iteratedDeriv 0 f y) 0 x := by
    rw [hg]
    exact hasDerivAt_const x 0
  have d0 : HasDerivAt (iteratedDeriv 0 f) (iteratedDeriv 1 f x) x := hasDerivAt_iter f hf 0 x
  have d1 : HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f x) x := hasDerivAt_iter f hf 1 x
  have d2 : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f x) x := hasDerivAt_iter f hf 2 x
  have h1 := (((hasDerivAt_id' x).mul d2).add (d1.const_mul c)).add ((hasDerivAt_id' x).mul d0)
  have key := h0.unique h1
  linear_combination -key

theorem oSp (x : ℝ) : x * iteratedDeriv 3 (besselS (-1 / 4)) x + (3 / 2) * iteratedDeriv 2 (besselS (-1 / 4)) x
    + iteratedDeriv 0 (besselS (-1 / 4)) x + x * iteratedDeriv 1 (besselS (-1 / 4)) x = 0 := by
  have h := ode_deriv_gen (besselS (-1 / 4)) (besselS_contDiff _ (by norm_num)) (1 / 2) oS x
  linear_combination h

theorem oTp (x : ℝ) : x * iteratedDeriv 3 (besselS (1 / 4)) x + (5 / 2) * iteratedDeriv 2 (besselS (1 / 4)) x
    + iteratedDeriv 0 (besselS (1 / 4)) x + x * iteratedDeriv 1 (besselS (1 / 4)) x = 0 := by
  have h := ode_deriv_gen (besselS (1 / 4)) (besselS_contDiff _ (by norm_num)) (3 / 2) oT x
  linear_combination h

theorem RS (a : ℝ) : (a ^ 2 / 4) * Uf 2 a + (1 / 2) * Uf 1 a + (a ^ 2 / 4) * Uf 0 a = 0 := by
  have h := oS (a ^ 2 / 4)
  unfold Uf
  linear_combination h

theorem RSp (a : ℝ) : (a ^ 2 / 4) * Uf 3 a + (3 / 2) * Uf 2 a + Uf 0 a + (a ^ 2 / 4) * Uf 1 a = 0 := by
  have h := oSp (a ^ 2 / 4)
  unfold Uf
  linear_combination h

theorem RT (a : ℝ) : (a ^ 2 / 4) * Vf 2 a + (3 / 2) * Vf 1 a + (a ^ 2 / 4) * Vf 0 a = 0 := by
  have h := oT (a ^ 2 / 4)
  unfold Vf
  linear_combination h

theorem RTp (a : ℝ) : (a ^ 2 / 4) * Vf 3 a + (5 / 2) * Vf 2 a + Vf 0 a + (a ^ 2 / 4) * Vf 1 a = 0 := by
  have h := oTp (a ^ 2 / 4)
  unfold Vf
  linear_combination h

theorem hS_eq (x : ℝ) : hSeries x = Real.pi ^ 2 / 4 * Kf x := by
  unfold hSeries Kf Uf Vf
  simp only [iteratedDeriv_zero]
  ring

theorem hSeries_fun : hSeries = fun x => Real.pi ^ 2 / 4 * Kf x := funext hS_eq

theorem deriv_chain1 (c : ℝ) : deriv (fun x => c * Kf x) = fun t => c * E1f t :=
  funext fun t => ((hK_d t).const_mul c).deriv

theorem deriv_chain2 (c : ℝ) : deriv (fun x => c * E1f x) = fun t => c * E2f t :=
  funext fun t => ((hE1_d t).const_mul c).deriv

theorem deriv_chain3 (c : ℝ) : deriv (fun x => c * E2f x) = fun t => c * E3f t :=
  funext fun t => ((hE2_d t).const_mul c).deriv

theorem iter2_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

theorem iter3_eq (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iter2_eq]

theorem iter2_fun (c : ℝ) : iteratedDeriv 2 (fun x => c * Kf x) = fun t => c * E2f t := by
  rw [iter2_eq, deriv_chain1, deriv_chain2]

theorem iter3_fun (c : ℝ) : iteratedDeriv 3 (fun x => c * Kf x) = fun t => c * E3f t := by
  rw [iter3_eq, deriv_chain1, deriv_chain2, deriv_chain3]

theorem hSeries_ode (a : ℝ) :
    iteratedDeriv 3 hSeries a + a ^ 2 * deriv hSeries a + a * hSeries a = 0 := by
  rw [hSeries_fun, iter3_fun, deriv_chain1]
  beta_reduce
  unfold E3f E1f Kf
  linear_combination (Real.pi ^ 2 / 4) * (((((Real.sqrt 8 * a) * Uf 0 a) + (((((1 : ℝ) / 2) * (-Real.sqrt 2)) * Vf 0 a) * (a * a)))) * RSp a + (((((1 / Real.sqrt 8) * Vf 0 a) * ((a * a) * a)) + (((((1 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 0 a) * (a * a)))) * RTp a + (((((((3 : ℝ)) * (-Real.sqrt 2)) * Vf 0 a) + (((((3 : ℝ)) * Real.sqrt 8) * a) * Uf 1 a)) + (((((3 : ℝ) / 2) * (-Real.sqrt 2)) * Vf 1 a) * (a * a)))) * RS a + ((((((-Real.sqrt 2) * Uf 0 a) + (((((3 : ℝ)) * (1 / Real.sqrt 8)) * Vf 1 a) * ((a * a) * a))) + (((((8 : ℝ)) * (1 / Real.sqrt 8)) * a) * Vf 0 a)) + (((((3 : ℝ) / 2) * (-Real.sqrt 2)) * Uf 1 a) * (a * a)))) * RT a)

theorem Uf_zero0 : Uf 0 0 = 1 / Real.Gamma (3 / 4) := by
  have h := besselS_zero (-1 / 4) (by norm_num)
  rw [show (-1 / 4 : ℝ) + 1 = 3 / 4 by norm_num] at h
  unfold Uf
  rw [iteratedDeriv_zero, show ((0 : ℝ) ^ 2 / 4) = 0 by norm_num, h]

theorem Vf_zero0 : Vf 0 0 = 1 / Real.Gamma (5 / 4) := by
  have h := besselS_zero (1 / 4) (by norm_num)
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num] at h
  unfold Vf
  rw [iteratedDeriv_zero, show ((0 : ℝ) ^ 2 / 4) = 0 by norm_num, h]

theorem Uf_one0 : Uf 1 0 = 0 := by
  unfold Uf
  rw [iteratedDeriv_one, show ((0 : ℝ) ^ 2 / 4) = 0 by norm_num]
  exact deriv_besselS_zero (-1 / 4) (by norm_num)

theorem Vf_one0 : Vf 1 0 = 0 := by
  unfold Vf
  rw [iteratedDeriv_one, show ((0 : ℝ) ^ 2 / 4) = 0 by norm_num]
  exact deriv_besselS_zero (1 / 4) (by norm_num)

theorem hSeries_zero : hSeries 0 = Real.pi ^ 2 * Real.sqrt 8 / (4 * Real.Gamma (3 / 4) ^ 2) := by
  have h1 := besselS_zero (-1 / 4) (by norm_num)
  have h2 := besselS_zero (1 / 4) (by norm_num)
  rw [show (-1 / 4 : ℝ) + 1 = 3 / 4 by norm_num] at h1
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num] at h2
  unfold hSeries
  rw [show ((0 : ℝ) ^ 2 / 4) = 0 by norm_num, h1, h2]
  ring

theorem deriv_hSeries_zero :
    deriv hSeries 0 = -(Real.pi ^ 2 * Real.sqrt 2 / (4 * (Real.Gamma (3 / 4) * Real.Gamma (5 / 4)))) := by
  rw [hSeries_fun, deriv_chain1]
  show Real.pi ^ 2 / 4 * E1f 0 = _
  unfold E1f
  rw [Uf_one0, Vf_one0, Uf_zero0, Vf_zero0]
  ring

theorem iteratedDeriv_two_hSeries_zero :
    iteratedDeriv 2 hSeries 0 = Real.pi ^ 2 / (2 * Real.sqrt 8 * Real.Gamma (5 / 4) ^ 2) := by
  rw [hSeries_fun, iter2_fun]
  show Real.pi ^ 2 / 4 * E2f 0 = _
  unfold E2f
  rw [Uf_one0, Vf_one0, Vf_zero0]
  ring

theorem hSeries_contDiff : ContDiff ℝ ∞ hSeries := by
  rw [hSeries_fun]
  have hS : ContDiff ℝ ∞ (besselS (-1 / 4)) := besselS_contDiff _ (by norm_num)
  have hT : ContDiff ℝ ∞ (besselS (1 / 4)) := besselS_contDiff _ (by norm_num)
  have hKc : ContDiff ℝ ∞ Kf := by
    unfold Kf Uf Vf
    simp only [iteratedDeriv_zero]
    fun_prop
  exact contDiff_const.mul hKc

theorem hBessel_eq_hSeries (a : ℝ) (ha : 0 < a) : hBessel a = hSeries a := by
  have hx : (0 : ℝ) < a ^ 2 / 4 := by positivity
  have hw : (0 : ℝ) < a ^ 2 / 4 / 2 := by positivity
  have hJ1 := besselJ_eq (-1 / 4) (a ^ 2 / 4) (by norm_num) hx
  have hJ2 := besselJ_eq (1 / 4) (a ^ 2 / 4) (by norm_num) hx
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (a ^ 2 / 4 / 2) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hqpos : 0 < q := by
    rw [hq]
    exact Real.rpow_pos_of_pos hw _
  have hq4 : q ^ 4 = a ^ 2 / 4 / 2 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    norm_num
  have hneg : (a ^ 2 / 4 / 2) ^ (-1 / 4 : ℝ) = q⁻¹ := by
    rw [hq, show (-1 / 4 : ℝ) = -(1 / 4) by norm_num, Real.rpow_neg hw.le]
  have hpos : (a ^ 2 / 4 / 2) ^ (1 / 4 : ℝ) = q := hq.symm
  have hs8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hs8pos : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hq2 : q ^ 2 = a / Real.sqrt 8 := by
    have h1 : (q ^ 2) ^ 2 = (a / Real.sqrt 8) ^ 2 := by
      rw [div_pow, hs8, show (q ^ 2) ^ 2 = q ^ 4 by ring, hq4]
      ring
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h1
  have hqq : q⁻¹ * q = 1 := inv_mul_cancel₀ hqpos.ne'
  unfold hBessel hSeries
  rw [hJ1, hJ2, hneg, hpos]
  have e1 : (q⁻¹ * besselS (-1 / 4) (a ^ 2 / 4)) ^ 2
      = Real.sqrt 8 / a * besselS (-1 / 4) (a ^ 2 / 4) ^ 2 := by
    rw [mul_pow, inv_pow, hq2, inv_div]
  have e2 : (q * besselS (1 / 4) (a ^ 2 / 4)) ^ 2
      = a / Real.sqrt 8 * besselS (1 / 4) (a ^ 2 / 4) ^ 2 := by
    rw [mul_pow, hq2]
  have e3 : Real.sqrt 2 * (q⁻¹ * besselS (-1 / 4) (a ^ 2 / 4)) * (q * besselS (1 / 4) (a ^ 2 / 4))
      = Real.sqrt 2 * (besselS (-1 / 4) (a ^ 2 / 4) * besselS (1 / 4) (a ^ 2 / 4)) := by
    linear_combination (Real.sqrt 2 * besselS (-1 / 4) (a ^ 2 / 4) * besselS (1 / 4) (a ^ 2 / 4)) * hqq
  rw [e1, e2, e3]
  have ha0 : a ≠ 0 := ha.ne'
  have hs0 : Real.sqrt 8 ≠ 0 := hs8pos.ne'
  field_simp

end Painleve
