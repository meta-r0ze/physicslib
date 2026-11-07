import PMFlavor.FlavourCoherence
import PMFlavor.LeptonAxisRestriction

/-! **Experimental/candidate module.**

# Per-step contract interface

A per-step contract restores the maintained reference after every event, not only
at cycle end.  This is the state-level counterpart of exact phase restoration.
-/

noncomputable section
namespace PMFlavor.PerStepContract

open PMFlavor.LeptonAxisRestriction

/-- Exact one-step state restoration. -/
def PerStepStateRestores (E : Equiv.Perm Packet) (ref : Packet) : Prop :=
  E ref = ref

/-- A per-step restoration plus a repair fixing the reference gives the cycle
restoration used by `LeptonAxisRestriction`. -/
theorem perStep_to_cycle (E rep : Equiv.Perm Packet) (ref : Packet)
    (hstep : PerStepStateRestores E ref) (hrep : rep ref = ref) :
    rep (E ref) = ref := by
  rw [hstep, hrep]

/-- Exact phase restoration is the phase-level per-step condition. -/
def PerStepPhaseRestores (phaseStep : ℝ) : Prop :=
  PMFlavor.FlavourCoherence.perStepRestores phaseStep

end PMFlavor.PerStepContract
