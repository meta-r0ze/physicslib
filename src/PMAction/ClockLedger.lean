import PMAction.Machine.CarrierResponse

/-!
# The clock and event ledger: a factor costs its flags

REVIEW B.4 noted that "four factor applications are not four primitive E8 events". In Persistence
Mechanics the priced event is a flag: a readout of change, repaired by `m` primitive events at
the common toll (`CarrierResponse.repairCost`). So a factor application costs its expected
flags, not one event:

* `tick_cost`: a tick of four unitary factors costs `(toll·m/2) Σⱼ (1 − Re tr Fⱼ / N)`.
* `identity_free`: a factor that changes nothing costs nothing.
* `clock_step_flag`: the clock advance (the cyclic shift of the four phases, which fixes no phase)
  raises a flag with probability `1/2`.
* `clock_tick_cost`: so the clock itself costs `4 × ½ = 2` flags, `2·toll·m`, per tick.

With `toll·m` fixed by the electric calibration (`PMConstants.EventStiffness.calibration`), every
term is a number. For a factor `e^{−iτH}` the flag probability `(1 − Re tr e^{−iτH}/N)/2` vanishes
quadratically as `τ → 0`, so the factors' share of the tick cost is controlled by the tick size;
the clock's share is fixed.
-/

noncomputable section
namespace PMAction.ClockLedger
open Matrix CarrierResponse InterferenceReadout

section General
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **A tick's cost is the sum of its factors' flags.** -/
theorem tick_cost (toll : ℝ) (m : ℕ) (F : Fin 4 → Matrix ι ι ℂ)
    (hF : ∀ j, F j ∈ unitary (Matrix ι ι ℂ)) :
    ∑ j, repairCost toll m (F j) =
      (toll * m / 2) * ∑ j, (1 - (F j).trace.re / Fintype.card ι) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => trace_cost toll m (F j) (hF j)

/-- **Doing nothing is free.** -/
theorem identity_free (toll : ℝ) (m : ℕ) : repairCost toll m (1 : Matrix ι ι ℂ) = 0 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [trace_cost toll m 1 (one_mem _)]
  simp [Matrix.trace_one, hn]

end General

/-- **The clock advance flags half the time.** -/
theorem clock_step_flag : meanFlag ((finRotate 4).permMatrix ℂ) = 1 / 2 := by
  rw [mean_trace _ (perm_unitary _), CarrierCost.trace_fixed,
    show (CarrierCost.fixed (finRotate 4)).card = 0 by decide]
  simp

/-- **The clock costs two flags per tick.** -/
theorem clock_tick_cost (toll : ℝ) (m : ℕ) :
    ∑ _j : Fin 4, repairCost toll m ((finRotate 4).permMatrix ℂ) = 2 * toll * m := by
  simp only [repair_cost, clock_step_flag, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

end PMAction.ClockLedger
