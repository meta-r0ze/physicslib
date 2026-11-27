import PMElementaryParticles.ChannelRecord
import PMElementaryParticles.CommonComparator

/-!
# Conditional Map comparison cost per period

The new frequency premise is named once in SCOPE. ChecksOnce is its finite
binary-record interpretation: the period's list of check positions visits each
retained bit exactly once. It specifies no reference or encoding.

The primitive receiver flag is one for differing Boolean basis values and zero
for equal values. The normalized receiver flag is used, NOT CommonResponse's
half-sized identity link flag (CommonComparator.exchangeFlag_eq_two_linkFlag).
For a localized packet a registration is a stream reversal, by the existing
ReversalEvents.registration_eq_reversal / registrations_eq_reversals theorems.
This module proves that their once-only sum is the Hamming distance and prices
it with OccupancyCost. It does not use baseline tollTerm as an event price.

The theorem is about the specified binary comparison account. Producing the
full channel/generation bits at native comparator ports, preserving the actual
retained reference, scheduling the checks and supplying a shared StrongMap
decoder remain realization obligations. Injective classical encodings do not
supply those operations. PMSubstrate.Pillars.map_maintains bounds a SUPPLIED
correction recurrence; it supplies no record, reference, or check frequency.
Nor is comparison a proof that the correction restores a conserved identity.

The original one-reversal account already includes a coarse comparison. Adding
it to this full comparison account requires disjoint-event ownership; automatic
addition would risk charging one event twice. Other physical costs remain open.
-/

noncomputable section
namespace PMElementaryParticles.MapMaintenance
open PMKAutomaton PMSubstrate.OccupancyCost

/-- The period has one check position for each retained binary distinction. -/
def ChecksOnce {I : Type*} (schedule : I → I) : Prop := Function.Bijective schedule

/-- One native Boolean basis comparison with the exchange guard enabled. -/
def comparisonState (a b : Bool) : RingReceiver.State 43 :=
  (0,(fun _ => (true,false),(fun _ => false,fun _ => (a,b))))

theorem native_boolean_flag (a b : Bool) :
    RingReceiver.receiverFlag true (comparisonState a b) 0 =
      ((if a ≠ b then 1 else 0 : ℕ) : ℝ) := by
  rw [RingReceiver.receiver_flag_eq]
  cases a <;> cases b <;>
    norm_num [comparisonState,RingReceiver.arrivals,PMAction.OpenReferenceFlow.streamShift,RingReceiver.exchange]

/-- This supplied localized basis exchange is one registration and one reversal. -/
theorem native_registration_is_reversal (b : Bool) :
    let r := fun _ : Fin 43 => (true,false)
    let s : PMElementaryParticles.ReversalEvents.Located 43 := (0,b)
    PMElementaryParticles.RingRates.tickCount true r (PMElementaryParticles.ReversalEvents.ports s) = 1 ∧
      PMElementaryParticles.ReversalEvents.reversal true r s = 1 := by
  dsimp only
  rw [PMElementaryParticles.ReversalEvents.registration_eq_reversal]
  cases b <;> exact ⟨rfl,rfl⟩

/-- Actual differing checks in the supplied period, at the existing unit event price. -/
def comparisonFootprint {I : Type*} [Fintype I] (record reference : I → Bool) (schedule : I → I) : Footprint :=
  { events := ∑ t, if record (schedule t) ≠ reference (schedule t) then 1 else 0 }

/-- Conditional frequency theorem. It does not choose record, reference, or an implementation. -/
theorem checks_once_events {I : Type*} [Fintype I] (record reference : I → Bool)
    (schedule : I → I) (h : ChecksOnce schedule) :
    (comparisonFootprint record reference schedule).events = hammingDist record reference := by
  change (∑ t, if record (schedule t) ≠ reference (schedule t) then 1 else 0) = _
  rw [hammingDist,Finset.card_filter]
  exact Fintype.sum_bijective schedule h _ _ (fun _ => rfl)

theorem checks_once_cost {I : Type*} [Fintype I] (record reference : I → Bool)
    (schedule : I → I) (h : ChecksOnce schedule) :
    cost (comparisonFootprint record reference schedule) = (hammingDist record reference : ℝ) := by
  have he := checks_once_events record reference schedule h
  have hc : cost (comparisonFootprint record reference schedule) =
      ((comparisonFootprint record reference schedule).events : ℝ) := by
    simp [cost,comparisonFootprint]
  rw [hc,he]

/-- The account equals the sum of the certified native Boolean comparison flags. -/
theorem cost_eq_native_flags {I : Type*} [Fintype I] (record reference : I → Bool)
    (schedule : I → I) :
    cost (comparisonFootprint record reference schedule) =
      ∑ t, RingReceiver.receiverFlag true (comparisonState (record (schedule t)) (reference (schedule t))) 0 := by
  simp only [native_boolean_flag]
  simp [comparisonFootprint,cost,Nat.cast_sum]

/-- The existing two-bit record adapter agrees with the shared Hamming API. -/
theorem coarse_hamming_agrees (a b : HeavyFlipControl.Record) :
    IsolatedExcitation.hamming a b = hammingDist ![a.1,a.2] ![b.1,b.2] := by
  rcases a with ⟨a1,a2⟩; rcases b with ⟨b1,b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> decide +kernel

/-- Reuses writeFlagCount_eq_hamming (formerly the bitToll/Hamming bridge). -/
theorem coarse_comparison_cost (colour : Bool) (c : PMConstants.PacketGaugeActions.Channels) :
    cost (comparisonFootprint
      ![(HeavyFlipControl.labelRecord c).1,(HeavyFlipControl.labelRecord c).2]
      ![(IsolatedExcitation.refRecord colour).1,(IsolatedExcitation.refRecord colour).2] id) =
      WireSchedule.writeFlagCount colour c := by
  rw [checks_once_cost _ _ id Function.bijective_id,
    IsolatedExcitation.writeFlagCount_eq_hamming,coarse_hamming_agrees]

/-- Canonical binary channel chart: at most four comparison reversals. -/
theorem channel_check_bound (c : PMConstants.PacketGaugeActions.Channels)
    (r : Fin 4 → Bool) (s : Fin 4 → Fin 4) (h : ChecksOnce s) :
    (comparisonFootprint (ChannelRecord.word c) r s).events ≤ 4 := by
  rw [checks_once_events _ _ _ h]
  exact ChannelRecord.channel_distance_bound c r

/-- Channel plus native generation-key bits: at most six, not the declared down count nine. -/
theorem generated_check_bound (c : PMConstants.PacketGaugeActions.Channels) (g : EPSpine.Generation)
    (r : Fin 4 ⊕ Fin 2 → Bool) : hammingDist (ChannelRecord.generatedWord c g) r <
      PMSubstrate.E8Values.D+PMSubstrate.E8Values.sigma := by
  have hb := ChannelRecord.generated_distance_bound c g r
  norm_num at *
  omega

end PMElementaryParticles.MapMaintenance
