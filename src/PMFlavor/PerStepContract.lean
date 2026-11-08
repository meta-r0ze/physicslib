import PMFlavor.FlavourCoherence
import PMFlavor.LeptonAxisRestriction

/-! **Experimental/candidate module.**

# Per-step contract: the lepton-axis restriction at every tick

A per-step contract restores the maintained reference after *every* event, not
only at cycle end. This is the state-level counterpart of exact phase
restoration.

`LeptonAxisRestriction.cycle_root_axis_zero` derives `R 0 = 0` from restoration
at the end of a one-event cycle. A check *only* at cycle end is too weak:
`sampleEvent` is an involution, so a cycle containing it twice returns to the
reference while touching the lepton axis in between (Gap A there). Under
per-step maintenance each step must restore, so the restriction holds for every
event (`run_roots_axis_zero`) and that bypass is excluded
(`perCycle_does_not_imply_perStep` formalizes the separation).
-/

noncomputable section
namespace PMFlavor.PerStepContract

open PMConstants.CarrierActions PMConstants.CarrierRepresentation PMConstants.RequirementTable
open PMAction.CarrierEvents
open PMSubstrate.ChannelSymmetry
open PMFlavor.LeptonAxisRestriction PMFlavor.MassTermLaw

/-- Exact one-step state restoration. -/
def PerStepStateRestores (E : Equiv.Perm Packet) (ref : Packet) : Prop :=
  E ref = ref

/-- A per-step restoration plus a repair fixing the reference gives the cycle
restoration used by `LeptonAxisRestriction`. -/
theorem perStep_to_cycle (E rep : Equiv.Perm Packet) (ref : Packet)
    (hstep : PerStepStateRestores E ref) (hrep : rep ref = ref) :
    rep (E ref) = ref := by
  rw [PerStepStateRestores] at hstep
  rw [hstep, hrep]

/-- **The restriction follows from one step.** If the event itself restores the
reference, any declared root it realizes avoids the lepton axis. This is the
per-step counterpart of `cycle_root_axis_zero`, with the repair taken to be the
identity. -/
theorem perStep_root_axis_zero (E : Equiv.Perm Packet) (ref : Packet)
    (href : channelType ref = Ty.L)
    (R : V4) (hR : R ∈ roots)
    (hstep : PerStepStateRestores E ref)
    (hE : vector (carried (E ref)) =
      PMSubstrate.ChannelSymmetry.refl (half R) (vector (carried ref))) :
    R 0 = 0 := by
  rw [PerStepStateRestores] at hstep
  exact cycle_root_axis_zero E (Equiv.refl Packet) ref (fun _ => rfl)
    (by simpa using hstep) href R hR hE

/-- A per-step-maintained run: every step's event is followed by a
type-preserving repair that restores the maintained reference. -/
def MaintainedRun (ref : Packet)
    (steps : List (Equiv.Perm Packet × Equiv.Perm Packet × V4)) : Prop :=
  ∀ E rep R, (E, rep, R) ∈ steps →
    (∀ v : Packet, channelType (rep v) = channelType v) ∧ rep (E ref) = ref

/-- **Every event in a per-step-maintained run avoids the lepton axis.** This is
`cycle_root_axis_zero` applied at each tick, so Gap A of
`LeptonAxisRestriction` — a per-cycle check admits paired lepton-touching
events — is excluded because the run restores after every step. -/
theorem run_roots_axis_zero
    (ref : Packet) (href : channelType ref = Ty.L)
    (steps : List (Equiv.Perm Packet × Equiv.Perm Packet × V4))
    (h : MaintainedRun ref steps)
    (hR : ∀ E rep R, (E, rep, R) ∈ steps → R ∈ roots)
    (hE : ∀ E rep R, (E, rep, R) ∈ steps →
      vector (carried (E ref)) = PMSubstrate.ChannelSymmetry.refl (half R) (vector (carried ref))) :
    ∀ E rep R, (E, rep, R) ∈ steps → R 0 = 0 := by
  intro E rep R hmem
  obtain ⟨htype, hrestore⟩ := h E rep R hmem
  exact cycle_root_axis_zero E rep ref htype hrestore href R (hR E rep R hmem) (hE E rep R hmem)

/-- `sampleEvent` is not per-step restoring: it sends the `L`-type reference off
the lepton axis. -/
theorem sampleEvent_not_perStep (ref : Packet) (href : channelType ref = Ty.L) :
    ¬ PerStepStateRestores sampleEvent ref := by
  intro hstep
  rw [PerStepStateRestores] at hstep
  obtain ⟨v, hvrfl, hv⟩ := reference_is_left_lepton ref href
  subst hvrfl
  have hbad := sample_event_breaks_type v hv
  have htype : channelType (sampleEvent (Sum.inl v)) = Ty.L := by
    rw [hstep, href]
  exact hbad (by simpa [sampleEvent] using htype)

/-- **Gap A is closed.** The involution `sampleEvent` restores any state after
*two* applications, so a cycle-end check accepts it; a per-step-maintained run
does not, because its first step already fails to restore. -/
theorem sampleEvent_pair_not_maintained (ref : Packet) (href : channelType ref = Ty.L) :
    ¬ MaintainedRun ref
      [(sampleEvent, Equiv.refl Packet, root), (sampleEvent, Equiv.refl Packet, root)] := by
  intro h
  obtain ⟨_, hrestore⟩ := h sampleEvent (Equiv.refl Packet) root (by simp)
  exact sampleEvent_not_perStep ref href (by rw [PerStepStateRestores]; exact hrestore)

/-- **Per-cycle restoration does not imply per-step maintenance (Gap A).** The two
`sampleEvent`s restore the reference end-to-end, yet the run is not per-step
maintained: the first step already leaves the `L` reference. So a cycle-end-only
contract is provably insufficient for the restriction `R 0 = 0`; the per-step
condition (`MaintainedRun`) is the right one. -/
theorem perCycle_does_not_imply_perStep (ref : Packet) (href : channelType ref = Ty.L) :
    sampleEvent (sampleEvent ref) = ref ∧
      ¬ MaintainedRun ref
        [(sampleEvent, Equiv.refl Packet, root), (sampleEvent, Equiv.refl Packet, root)] :=
  ⟨sampleEvent_involutive ref, sampleEvent_pair_not_maintained ref href⟩


/-- Exact phase restoration is the phase-level per-step condition. -/
def PerStepPhaseRestores (phaseStep : ℝ) : Prop :=
  PMFlavor.FlavourCoherence.perStepRestores phaseStep

end PMFlavor.PerStepContract
