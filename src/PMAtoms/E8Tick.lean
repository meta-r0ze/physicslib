import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# E8 tick

The substrate clock period is `Δ = 43` in `m_e` units.  This module contains
only the E8 period.  The SI conversion lives in `E8TickUnit` and is explicitly a
comparison/unit input.
-/

noncomputable section
namespace PMAtoms

/-- E8 clock period in `m_e` units. -/
def e8Tick : ℝ := (PMSubstrate.E8Values.Delta : ℝ)

theorem e8Tick_eq : e8Tick = 43 := by
  unfold e8Tick
  norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.baseline]

/-- Number of E8 ticks in a lifetime measured in `m_e` units. -/
def lifetimeTicks (tau : ℝ) : ℝ := tau / e8Tick

theorem lifetimeTicks_eq (tau : ℝ) : lifetimeTicks tau = tau / e8Tick := rfl

end PMAtoms
