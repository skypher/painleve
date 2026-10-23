import Painleve.MainOf
import Painleve.Blocks
import Painleve.BesselMatch
import Painleve.Limits

/-!
# Theorem 1.1 of `paper.tex`

`main_theorem : Stmt_main` — for `a > 0`, every leading Gram matrix of the
Felder–Hoppe form for `d = 4` is nondegenerate with positive signed norms
(Felder–Hoppe Conjecture 3.6, `d = 4`, `a > 0`), and the Bessel initial values
extend uniquely to a positive solution `v_n = 𝔥_{n+1}/(a 𝔥_n)` of the quartic
recurrence.
-/

namespace Painleve

/-- `∫ ρ_a = h(a)` for `a > 0` (Lemma 4.1 with `λ = 1`). -/
theorem hPlanar_eq_hBessel' (a : ℝ) (ha : 0 < a) : hPlanar a = ((hBessel a : ℝ) : ℂ) :=
  hPlanar_eq_hBessel tendsto_Phi00 tendsto_a_Phi10 tendsto_Phi11
    gamma_match0 gamma_match1 gamma_match2 a ha

/-- **Theorem 1.1.** -/
theorem main_theorem : Stmt_main :=
  main_of (fun a ha r k hr => blockGram_sign a ha r k hr) hPlanar_eq_hBessel'

end Painleve
