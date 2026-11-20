import PMElementaryParticles.IsolatedExcitation
import PMElementaryParticles.WireSchedule
import PMElementaryParticles.ProtocolInventory
import PMElementaryParticles.WireReferenceCost

/-!
# Conditional mixed-witness, hand-booked account

**This is not a trace of `IsolatedExcitation.occupiedInput`.**  The receiver
term below iterates `RingReceiver.mixedBasisRing`, the mixed-request
contention witness, through `PMTransport.Values.mixedReceiverFlagAt`.  The
booked slot sets are hand definitions: `hold` books one slot and `FIFO`
books all 43.  Those slot sets are not derived from the Transport packet
lifts.  The receiver registrations and the record Toll are kept as separate
columns: no certified result puts them in one ledger.

The numbers in this file are therefore **conditional (mixed witness,
hand-booked)**.  The isolated-input trace must be computed on a state built
from `IsolatedExcitation.occupiedInput`; that is a separate task.  Nothing
below claims the isolated excitation has been run.

The heavy record reference is a certified two-element family; this file
does not select it.  The retained ring exports nothing, so its erased-bit
count is zero for that retained ring (`BoundaryErasure.ring_cycle_erasure`).
-/

noncomputable section
namespace PMElementaryParticles.IsolatedExcitation

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.ProtocolToll
open PMElementaryParticles.WireSchedule
open PMAction Matrix

/-! ## One full clock period

`Delta = 43`.  The candidate coordinates are the bank motion (`fifo`),
the receiver rule (`either`, false = AND, true = OR) and the excursion
placement (`shifted`).  The retained ring exports nothing, so the erased
count is zero for every tick (`BoundaryErasure.ring_cycle_erasure`).
-/

abbrev Delta := PMTransport.Values.Delta

def starts (shifted : Bool) : Fin Delta := (PMTransport.Values.excursionSlots shifted).1

/-- The booked part of the clock.  A held bank books the phase at which it is
held; FIFO advances through the whole period and books every receiver visit. -/
def bookedSlots (fifo shifted : Bool) : Finset (Fin Delta) :=
  if fifo then Finset.univ else {starts shifted}

def bookedMask (fifo shifted : Bool) : Fin Delta → Bool :=
  fun t => decide (t ∈ bookedSlots fifo shifted)

theorem filter_bookedMask (fifo shifted : Bool) :
    Finset.univ.filter (fun t => bookedMask fifo shifted t = true) =
      bookedSlots fifo shifted := by
  ext t
  simp [bookedMask]

def bookedCount (fifo : Bool) : ℕ := if fifo then Delta else 1

theorem bookedCount_eq_card (fifo shifted : Bool) :
    bookedCount fifo = (bookedSlots fifo shifted).card := by
  cases fifo <;> simp [bookedCount, bookedSlots]

theorem bookedCount_fifo : bookedCount true = Delta := rfl

theorem bookedCount_hold : bookedCount false = 1 := rfl

/-- Booked receiver registrations in one period.  This is the trace's
registration count, not a supplied rate: `mixedReceiverFlagAt_eq` evaluates
every visited phase. -/
noncomputable def receiverToll (fifo either _shifted : Bool) : ℝ :=
  (bookedCount fifo : ℝ) * (if either then 1 else 0)

/-- The trace sum: the booked receiver registrations per period. -/
theorem receiverToll_eq_trace (fifo either shifted : Bool) :
    receiverToll fifo either shifted =
      ∑ t : Fin Delta,
        if bookedMask fifo shifted t then PMTransport.Values.mixedReceiverFlagAt either t else 0 := by
  unfold receiverToll bookedCount bookedMask bookedSlots
  cases fifo <;> cases either <;>
    simp [PMTransport.Values.mixedReceiverFlagAt_eq]

/-- No bit leaves the retained ring, hence no erased bit in the period. -/
theorem trace_erased (disposition : Fin Delta → PMTransport.BoundaryErasure.Disposition) :
    PMTransport.BoundaryErasure.cycleErased disposition (fun _ => none) = 0 :=
  (PMTransport.BoundaryErasure.ring_cycle_erasure disposition).1

/-! ## Booked Toll and amplitude, trace by trace -/

/-- The electron reference is the lepton column: every electron packet label
is colourless (`colourBulk false`), and the lepton-reference record gives
electron Toll one.  The same trace works for both electron wall labels. -/
def electronReference : Bool := false

theorem electron_reference_toll :
    WireSchedule.bitToll electronReference electronStatic = 1 := by
  simpa [electronReference] using (WireSchedule.lepton_tolls 0).1

/-- Booked Toll of a label on the trace.  The receiver registrations are the
common trace term; the record term is the certified two-bit record. -/
noncomputable def bookedToll (fifo either shifted : Bool) (reference : Bool)
    (label : Channels) : ℝ :=
  receiverToll fifo either shifted + WireSchedule.bitToll reference label

noncomputable def bookedAmplitude (fifo either shifted : Bool) (reference : Bool)
    (label : Channels) : ℝ :=
  PMAction.TollAmplitude.wireAmplitude
    (bookedToll fifo either shifted reference label)

/-- The electron trace's booked Toll, for the eight candidate rows. -/
noncomputable def electronToll (fifo either shifted : Bool) : ℝ :=
  bookedToll fifo either shifted electronReference electronStatic

theorem electronToll_eq (fifo either shifted : Bool) :
    electronToll fifo either shifted = receiverToll fifo either shifted + 1 := by
  rw [electronToll, bookedToll, electron_reference_toll]

theorem electronToll_hold_AND (shifted : Bool) :
    electronToll false false shifted = 1 := by
  rw [electronToll_eq, receiverToll]; simp

theorem electronToll_hold_OR (shifted : Bool) :
    electronToll false true shifted = 2 := by
  rw [electronToll_eq, receiverToll]; norm_num [bookedCount_hold]

theorem electronToll_fifo_AND (shifted : Bool) :
    electronToll true false shifted = 1 := by
  rw [electronToll_eq, receiverToll]; simp

theorem electronToll_fifo_OR (shifted : Bool) :
    electronToll true true shifted = 44 := by
  rw [electronToll_eq, receiverToll]
  simp [bookedCount_fifo]
  norm_num

/-- The eight electron values.  Placement does not enter the per-period
count: the 43-phase clock is periodic, so both certified excursion starts
book the same number of visits. -/
theorem electronToll_cases (fifo either shifted : Bool) :
    electronToll fifo either shifted =
      if either then (if fifo then 44 else 2) else 1 := by
  cases fifo <;> cases either <;> simp [electronToll_hold_AND, electronToll_hold_OR,
    electronToll_fifo_AND, electronToll_fifo_OR]

noncomputable def electronAmplitude (fifo either shifted : Bool) : ℝ :=
  PMAction.TollAmplitude.wireAmplitude (electronToll fifo either shifted)

/-- The heavy writer is the down label at the direct address.  The trace
fixes its colour/lepton record columns but not which column is physical, so
both are carried. -/
noncomputable def heavyToll (fifo either shifted : Bool) (reference : Bool) (a : Fin 3) : ℝ :=
  bookedToll fifo either shifted reference (downStatic a)

noncomputable def heavyWeight (fifo either shifted : Bool) (reference : Bool) (a : Fin 3) : ℝ :=
  PMAction.TollAmplitude.wireAmplitude (heavyToll fifo either shifted reference a)

/-- The colour-reference heavy trace has Tolls `(2,1,0,1)` on
electron, down, up and neutrino. -/
theorem heavyToll_colour (fifo either shifted : Bool) (a : Fin 3) :
    bookedToll fifo either shifted true electronStatic = receiverToll fifo either shifted + 2 ∧
    bookedToll fifo either shifted true (downStatic a) = receiverToll fifo either shifted + 1 ∧
    bookedToll fifo either shifted true (upStatic a) = receiverToll fifo either shifted + 0 ∧
    bookedToll fifo either shifted true neutrinoStatic = receiverToll fifo either shifted + 1 := by
  obtain ⟨he, hu, hd⟩ := WireSchedule.colour_tolls a
  obtain ⟨hn', -⟩ := WireReferenceCost.neutral_slot_tolls
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bookedToll, he, hd, hu, hn']

/-- The lepton-reference heavy trace has Tolls `(1,2,1,0)`. -/
theorem heavyToll_lepton (fifo either shifted : Bool) (a : Fin 3) :
    bookedToll fifo either shifted false electronStatic = receiverToll fifo either shifted + 1 ∧
    bookedToll fifo either shifted false (downStatic a) = receiverToll fifo either shifted + 2 ∧
    bookedToll fifo either shifted false (upStatic a) = receiverToll fifo either shifted + 1 ∧
    bookedToll fifo either shifted false neutrinoStatic = receiverToll fifo either shifted + 0 := by
  obtain ⟨he, hu, hd⟩ := WireSchedule.lepton_tolls a
  obtain ⟨-, hn'⟩ := WireReferenceCost.neutral_slot_tolls
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bookedToll, he, hd, hu, hn']

/-! ## The down identity on the trace -/

/-- For the colour reference every candidate trace satisfies the down
geometric mean `s_d² = s_e · s_u`: the common receiver term cancels because
down's record Toll is the mean of electron's and up's. -/
theorem down_geometric_mean_colour (fifo either shifted : Bool) (a : Fin 3) :
    (bookedAmplitude fifo either shifted true (downStatic a)) ^ 2 =
      bookedAmplitude fifo either shifted true electronStatic *
        bookedAmplitude fifo either shifted true (upStatic a) := by
  obtain ⟨he, hu, hd⟩ := WireSchedule.colour_tolls a
  unfold bookedAmplitude bookedToll
  rw [he, hd, hu]
  unfold PMAction.TollAmplitude.wireAmplitude
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- The lepton reference does not satisfy the same identity on the same trace:
its record Tolls are `(1,2,1,0)`, so down sits one unit above the mean. -/
theorem down_geometric_mean_lepton_fails (fifo either shifted : Bool) (a : Fin 3) :
    (bookedAmplitude fifo either shifted false (downStatic a)) ^ 2 ≠
      bookedAmplitude fifo either shifted false electronStatic *
        bookedAmplitude fifo either shifted false (upStatic a) := by
  obtain ⟨he, hu, hd⟩ := WireSchedule.lepton_tolls a
  unfold bookedAmplitude bookedToll
  rw [he, hd, hu]
  unfold PMAction.TollAmplitude.wireAmplitude
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  intro h
  have hinj := Real.exp_injective h
  ring_nf at hinj
  linarith

/-! ## Conditional mixed-witness labels

These aliases make the status explicit at use sites.  They are the same
hand-booked mixed-witness values as above, not isolated-input traces.
-/

noncomputable def conditionalMixedElectronToll (fifo either shifted : Bool) : ℝ :=
  electronToll fifo either shifted

noncomputable def conditionalMixedHeavyToll (fifo either shifted : Bool)
    (reference : Bool) (a : Fin 3) : ℝ :=
  heavyToll fifo either shifted reference a

end PMElementaryParticles.IsolatedExcitation
