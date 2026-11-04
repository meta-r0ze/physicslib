import Mathlib.Tactic

/-!
# The rank rule for the beta coefficient fails its own universality test

`4_C_beta.tex` proposes the gauge (anti-screening) coefficient `11 = rank 8 + rank 3` and asks
that the same construction rules apply to every gauge theory. The one-loop gauge coefficient of
`SU(N)` is `(11/3)N`; for the weak `SU(2)` it is `22/3`.

* `rank_rule_not_universal`: no sum of natural-number ranks equals `22/3`, so an integer rank
  composition cannot be the universal rule.
* `casimir_form`: the coefficient is `(11/3) C_A` with `C_A = N`. For colour `C_A = 3`, which is the
  colour-bulk dimension `σ − χ`; for the weak sector `C_A = 2 = χ`. Both values are reproduced,
  `11` and `22/3`, by one rule. The factor `11/3` itself is the standard one-loop result
  (paramagnetic `4` minus diamagnetic `1/3` per gauge mode); deriving it from the substrate
  response is the open obligation.
-/

namespace PMConstants.BetaUniversality

theorem rank_rule_not_universal : ∀ a b : ℕ, ((a + b : ℕ) : ℚ) ≠ 22/3 := by
  intro a b h
  have h3 : (3 : ℚ) * (a + b : ℕ) = 22 := by rw [h]; norm_num
  have : 3 * (a + b) = 22 := by exact_mod_cast h3
  omega

def gaugeCoeff (cA : ℚ) : ℚ := 11/3 * cA

theorem casimir_form : gaugeCoeff (5 - 2) = 11 ∧ gaugeCoeff 2 = 22/3 := by
  constructor <;> norm_num [gaugeCoeff]

end PMConstants.BetaUniversality
