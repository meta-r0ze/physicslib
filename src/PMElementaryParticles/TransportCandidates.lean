import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.QuarkMasses
import PMElementaryParticles.WireReferenceCost
import PMElementaryParticles.IsolatedReceiverTrace
import PMElementaryParticles.TierLedger
import PMKAutomaton.Values

/-!
# Transport candidates and the down protocol

This module held computation that was in `PMElementaryParticles.Values`. `Values` is now only the
library's read API.

## Finite KAutomaton witness family

These eight rows index the hold/FIFO, AND/OR and placement witnesses.
They do not enumerate all possible physical EP updates. The first two
projections are the bank motion and the receiver rule. The third is the
choice of excursion example. Physical readout and work remain inputs.

These rows are superseded as the EP program type by `EPSpine.Program` (one program on the
43-site ring, its generation from the glue coset). They stay here as a record of the old
uniform-field control. `e8p` does not read them.

## Down protocol

The colour reference, common bit price and all remaining paid work
are separate from the declared species ledger.
-/

namespace PMElementaryParticles.TransportCandidates

open PMConstants.PacketGaugeActions
open ProtocolInventory

abbrev Candidate := Bool × Bool × Bool

def bools : List Bool := [false, true]

def candidates : List Candidate :=
  bools.flatMap fun fifo => bools.flatMap fun either => bools.map fun shifted =>
    (fifo, either, shifted)

theorem candidates_complete : ∀ c : Candidate, c ∈ candidates := by
  decide +kernel

theorem candidates_count : candidates.length = 8 ∧ candidates.Nodup := by
  decide +kernel

def phases (c : Candidate) : Fin PMKAutomaton.Values.Delta × Fin PMKAutomaton.Values.Delta :=
  PMKAutomaton.Values.excursionSlots c.2.2

/-- Unit comparison registrations per tick at site zero if the mixed
basis input is supplied and all visits are booked. This is a receiver
account, not a physical EP writer cost. -/
def allBookedMixedRate (c : Candidate) : ℕ := if c.2.1 then 1 else 0

theorem allBookedMixedRate_eq (c : Candidate) :
    (allBookedMixedRate c : ℝ) =
      PMKAutomaton.Values.mixedReceiverRate c.2.1 (fun _ => true) := by
  rw [PMKAutomaton.Values.mixedReceiverRate_all_booked]
  by_cases h : c.2.1 <;> simp [allBookedMixedRate, h]

/-- The common input measures the writer's booked population. The reset
and other terms are actual paid work per input in this same account.
A negative colour-minus-lepton difference favours colour. -/
noncomputable def referenceDifference (c : Candidate)
    (bookedMass : Candidate → Channels → ℝ)
    (erased remaining : Candidate → Bool → ℝ) : ℝ :=
  2 * (∑ x ∈ Finset.univ.filter (fun x : Channels => ProtocolInventory.colourBulk x = false),
      bookedMass c x) - (∑ x, bookedMass c x) +
    (erased c true - erased c false) + (remaining c true - remaining c false)

theorem referenceDifference_eq (c : Candidate)
    (bookedMass : Candidate → Channels → ℝ)
    (erased remaining : Candidate → Bool → ℝ) :
    referenceDifference c bookedMass erased remaining =
      ((∑ x, bookedMass c x * WireSchedule.bitToll true x) + erased c true + remaining c true) -
      ((∑ x, bookedMass c x * WireSchedule.bitToll false x) + erased c false + remaining c false) := by
  unfold referenceDifference
  rw [← WireReferenceCost.booked_population_difference (bookedMass c)]
  ring

/-- Heavy-label amplitude on a supplied serial trace. The eligibility
proof uses the supplied admission predicate. Physical G, W and U are
needed to identify this trace with the row's realized writer. -/
noncomputable def heavyWeight {ticks : ℕ} (c : Candidate)
    (premises : Candidate → WireSchedule.Premises ticks)
    (trace : Candidate → WireSchedule.Schedule ticks)
    (_admitted : WireSchedule.admissible (premises c) (trace c) = true)
    (companionSetup : Candidate → Bool)
    (unpriced : Candidate → Channels → WireSchedule.Schedule ticks → ℝ) (label : Channels) : ℝ :=
  WireSchedule.amplitude (companionSetup c) (unpriced c) label (trace c)

/-- The common static-vector determinant response. T and U must
identify the offset and the detuning of the admitted trace. -/
theorem lightResponse (c : Candidate) (s : BaseProtocol) (hs : s ≠ .neutrino)
    (label : Channels) (detuning : Candidate → ℂ) (offset : Candidate → BaseProtocol → ℂ)
    (cycle : Candidate → Fin 3 → ℂ)
    (resonance : detuning c ^ 3 = -(cycle c 0 * cycle c 1 * cycle c 2)) :
    (ChargedInsertion.flip s label (detuning c) (offset c s) (cycle c)).det =
      if active label = false ∧ baseProtocol label = some s then detuning c ^ 2 * offset c s
      else 0 :=
  ChargedInsertion.det_flip_at_resonance s hs label _ _ _ resonance

def tier (c : Candidate) (identify : Candidate → TierLedger.WireTierAssignment)
    (protocol : BaseProtocol) (address : Fin 3) : ProtocolDynamics.Tier :=
  TierLedger.wireTier (identify c) protocol address

/-- [Premise] The existing species formulas on their declared tier rows,
in electron-mass units. The neutral sector has no mass ledger here. -/
noncomputable def declaredMass (protocol : BaseProtocol) (t : ProtocolDynamics.Tier) : Option ℝ :=
  match protocol, t.val with
  | .up, 0 => some QuarkMasses.up
  | .up, 2 => some QuarkMasses.charm
  | .up, 3 => some QuarkMasses.top
  | .down, 0 => some QuarkMasses.down
  | .down, 1 => some QuarkMasses.strange
  | .down, 2 => some QuarkMasses.bottom
  | .electron, 0 => some 1
  | .electron, 1 => some LeptonMasses.muon
  | .electron, 2 => some LeptonMasses.tau
  | _, _ => none

/-- Evaluate the declared mass ledger after the caller identifies the
wire tier for this candidate and address. -/
noncomputable def mass (c : Candidate) (identify : Candidate → TierLedger.WireTierAssignment)
    (protocol : BaseProtocol) (address : Fin 3) : Option ℝ :=
  declaredMass protocol (tier c identify protocol address)

/-- A numeric light-offset order is absent from the witness labels.
The operation and scaling law enter through the supplied offset. -/
def certifiedOffsetOrder (_c : Candidate) (_protocol : BaseProtocol) : Option ℕ := none

/-! ### Uniform control field, not one excitation

`uniformPorts` puts the packet on all sites and both streams.  Its receiver
column is zero under AND and OR because the arrivals are equal by construction.
This is **not** the one-excitation trace.  The localized embedding and its
occupancy check are in `IsolatedReceiverTrace`; the localized trace is not yet
reported here.  The number below is a uniform-field control, not a mass value.
-/

noncomputable def uniformTraceRegistrations (either : Bool) (c : Fin 3)
    (vacuum : IsolatedExcitation.VacuumLabel c) (packet : IsolatedExcitation.PacketLabel)
    (fields : IsolatedExcitation.ReceiverFields) : ℝ :=
  IsolatedExcitation.uniformReceiverColumn either c vacuum packet fields

theorem uniformTraceRegistrations_zero (either : Bool) (c : Fin 3)
    (vacuum : IsolatedExcitation.VacuumLabel c) (packet : IsolatedExcitation.PacketLabel)
    (fields : IsolatedExcitation.ReceiverFields) :
    uniformTraceRegistrations either c vacuum packet fields = 0 :=
  IsolatedExcitation.uniformReceiverColumn_eq_zero either c vacuum packet fields

noncomputable def isolatedRecordColumn (reference : Bool) (label : Channels) : ℝ :=
  IsolatedExcitation.isolatedRecordColumn reference label

end PMElementaryParticles.TransportCandidates

namespace PMElementaryParticles.DownProtocol

open ProtocolToll in
theorem down_colour_geometric_mean (price : ℝ) (a : Fin 3) :
    let s c := PMAction.TollAmplitude.wireAmplitude (price * WireSchedule.bitToll true c)
    s (downStatic a) ^ 2 = s electronStatic * s (upStatic a) := by
  simpa only [WireSchedule.bitToll, ElectricHeavyRecord.colour_reference_toll] using
    HeavyFlipRecords.down_geometric_mean price a

/-- [Premise] This is the declared down protocol ledger, with no
identification of an admitted wire address with a tier. -/
theorem down_declared_tiers :
    (TierLedger.tiersFor .down).map Fin.val = [0, 1, 2] := rfl

end PMElementaryParticles.DownProtocol
