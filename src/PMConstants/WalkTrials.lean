import PMAction.WalkReferenceProtocol
import PMAction.WalkReferenceCycle
import PMConstants.BudgetReadout

/-!
# Codex's finite walk protocol, read against the scalar ledger

Paper II now has a complete finite protocol (`WalkReferenceProtocol`, `WalkReferenceCycle`): one
`γ` coupling exchanges live and record packets losslessly, forward preparation forces the
quarter pulse, `N` prepared references support `N` closed trials, and every named operation is
priced. Three consequences for Paper III's ledger `(B − 1/43)/23`:

* `maintained_exactly` (reference persistence on a closed ring): on a ring of `R+1` cells with
  prepared records, the reference at the coupling site is restored on each of the first `R+1`
  trials (`ring_restores`); on trial `R+2` a non-reference old packet returns (`finite_horizon`).
  A closed finite region maintains a drifting reference for a bounded time; indefinite
  persistence needs an open supply of clean records.
* `instruction_ledgers_excluded` (net readout against instruction counts): with a common unit
  tariff, the protocol charges `4` named operations per trial (`step_price`) and `1` for the
  coupling alone. Neither fits `λ` as the budget. The net readout's `3` does. *Caution:* the three
  transport operations (hop, coin, phase) also number `3`, so `λ` cannot separate that count from
  the net readout; the net-readout reading rests on `BudgetReadout`/`TangentResponse`, not on `λ`.
* `preparation_renewal_allowed` (renewal at the preparation price): each renewal costs one seed
  preparation, response `(1 − cos(π/4))/2` (`WalkReferenceCoupling.preparation_response`), that is
  `1 − cos(π/4)` in units of one direction's response `1/2`. Charged once per cycle and spread over
  the 43 phases, the ledger stays in the `λ` window. So `BudgetReadout.renewal_per_direction_excluded`
  rules out only *per-direction* renewal pricing; at Codex's actual preparation price `λ` cannot
  tell whether renewal is charged to the budget.
-/

noncomputable section
namespace PMConstants.WalkTrials
open PMAction WalkReferenceCycle

/-- **A closed ring maintains the reference for exactly its record count.** -/
theorem maintained_exactly (R : ℕ) (s : State (Fin (R+1))) (reference : WalkReferenceCoupling.Doublet)
    (hr : ∀ x, (s x).2 = reference) (hold : (s ((finRotate (R+1))⁻¹ 0)).1 ≠ reference) :
    (∀ t, 0 < t → t ≤ R + 1 → (((advance 0 (finRotate (R+1)))^[t] s) 0).1 = reference) ∧
      (((advance 0 (finRotate (R+1)))^[R+2] s) 0).1 ≠ reference :=
  ⟨fun t h0 h1 => ring_restores R t h0 h1 s reference hr, finite_horizon R s reference hold⟩

/-- **Uniform instruction counts do not fit as the budget.** -/
theorem instruction_ledgers_excluded :
    (WalkReferenceProtocol.program.map (WalkReferenceProtocol.price 1 1 1 1)).sum = 4 ∧
      ¬ ((0.1286 : ℝ) < (4 - 1/43) / 23 ∧ (4 - 1/43 : ℝ) / 23 < 0.1300) ∧
      ¬ ((0.1286 : ℝ) < (1 - 1/43) / 23) ∧
      ((0.1286 : ℝ) < (3 - 1/43) / 23 ∧ (3 - 1/43 : ℝ) / 23 < 0.1300) := by
  refine ⟨by rw [WalkReferenceProtocol.step_price]; norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- **Renewal at the preparation price is not excluded.** -/
theorem preparation_renewal_allowed :
    let c := (1 - Real.cos (Real.pi / 4)) / 43
    (0.1286 : ℝ) < (3 - 1/43 - c) / 23 ∧ (3 - 1/43 - c) / 23 < 0.1300 := by
  intro c
  have hc : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have s1 : (1.414 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 2 < (1.415 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [c, hc]
  constructor <;> nlinarith

/-- The preparation price in units of one direction's response. -/
theorem preparation_in_direction_units :
    PMAction.CommonResponse.stateFlag WalkReferenceCoupling.preparation WalkReferenceCoupling.seed /
      (1 / 2) = 1 - Real.cos (Real.pi / 4) := by
  rw [WalkReferenceCoupling.preparation_response]; ring

end PMConstants.WalkTrials

