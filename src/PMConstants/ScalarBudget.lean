import Mathlib.Tactic

/-!
# The scalar ledger's budget is the integer 3

`λ = (B − 1/43)/23` with sync credit `1/43` (`RegulatoryBudget.clock_credit`). Measured
`λ = m_H²G_F/√2 = 0.12928 ± 0.00023` (from `m_H = 125.20 ± 0.11` GeV and `G_F`).

* `budget_unique`: among natural budgets `B`, only `B = 3` puts `λ` within `3σ`
  (`0.1286 < λ < 0.1300`). The count is `3`, matching both the colour-bulk dimension `σ − χ` and the
  number of generations (`Generations.three_pairs`); which of these the budget is remains open.
-/

namespace PMConstants.ScalarBudget

theorem budget_unique (B : ℕ) :
    ((0.1286 : ℚ) < ((B : ℚ) - 1/43) / 23 ∧ ((B : ℚ) - 1/43) / 23 < 0.1300) ↔ B = 3 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hB1 : (2.98 : ℚ) < B := by linarith
    have hB2 : (B : ℚ) < 3.02 := by linarith
    have : 2 < B := by exact_mod_cast (by linarith : (2 : ℚ) < B)
    have : B < 4 := by exact_mod_cast (by linarith : (B : ℚ) < 4)
    omega
  · rintro rfl; norm_num

end PMConstants.ScalarBudget
