import PMElementaryParticles.IsolatedReceiverTrace
import PMElementaryParticles.HeavyFlipRecords
import PMElementaryParticles.WireSchedule

/-!
# Candidate record-port identification (gap U)

**Candidate for gap U, hypothesis, not certified.**  The EP record Toll is a
count of exact record bits.  This file tests the candidate identification of
each record bit with one receiver encounter: live arrival = the corresponding
`labelRecord` bit, record arrival = the corresponding reference-record bit,
with exchange firing at the encounter.

The colour reference record is `(false,false)`; the lepton reference record is
`(true,false)` in the `(sector,position)` order of `labelRecord`.
-/

noncomputable section
namespace PMElementaryParticles.IsolatedExcitation

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.WireSchedule
open PMTransport

/-- Hamming distance of two 2-bit records. -/
def hamming (a b : Record) : ℕ :=
  (if a.1 ≠ b.1 then 1 else 0) + (if a.2 ≠ b.2 then 1 else 0)

/-- Candidate reference record: colour = all false, lepton = `(true,false)`
in `(sector,position)` order. -/
def refRecord (colourReference : Bool) : Record :=
  if colourReference then (false, false) else (true, false)

/-- Task H Step 1: the candidate reference record reproduces both EP rows for
all 16 labels. -/
theorem bitToll_eq_hamming :
    ∀ (colourReference : Bool) (c : Channels),
      WireSchedule.bitToll colourReference c =
        (hamming (labelRecord c) (refRecord colourReference) : ℝ) := by
  intro colourReference c
  cases colourReference
  · rw [WireSchedule.bitToll, ElectricHeavyRecord.phase_position,
      ElectricHeavyRecord.phase_sector_lepton_reference]
    unfold hamming refRecord
    rcases h : labelRecord c with ⟨s, p⟩
    cases s <;> cases p <;> norm_num
  · rw [WireSchedule.bitToll, ElectricHeavyRecord.phase_position,
      ElectricHeavyRecord.phase_sector]
    unfold hamming refRecord
    rcases h : labelRecord c with ⟨s, p⟩
    cases s <;> cases p <;> norm_num

/-- The colour row is exactly the true-bit count of `labelRecord`. -/
theorem colour_hamming (c : Channels) :
    (hamming (labelRecord c) (refRecord true) : ℝ) = HeavyFlipRecords.orbitRecordToll c := by
  rw [← bitToll_eq_hamming true c]
  simpa [WireSchedule.bitToll] using ElectricHeavyRecord.colour_reference_toll c

/-- Candidate identification structure for gap U.  This is a hypothesis. -/
structure RecordPortIdentification where
  reference : Bool
  /-- `b = 0` is the sector bit; `b = 1` is the position bit. -/
  live : Channels → Fin 2 → Bool
  record : Channels → Fin 2 → Bool
  live_sector : ∀ c, live c 0 = (labelRecord c).1
  live_position : ∀ c, live c 1 = (labelRecord c).2
  record_sector : ∀ c, record c 0 = (refRecord reference).1
  record_position : ∀ c, record c 1 = (refRecord reference).2

/-- Candidate identification for the colour reference. -/
def colourIdentification : RecordPortIdentification where
  reference := true
  live c b := if b = 0 then (labelRecord c).1 else (labelRecord c).2
  record _ b := if b = 0 then (refRecord true).1 else (refRecord true).2
  live_sector _ := rfl
  live_position _ := rfl
  record_sector _ := rfl
  record_position _ := rfl

/-- Candidate identification for the lepton reference. -/
def leptonIdentification : RecordPortIdentification where
  reference := false
  live c b := if b = 0 then (labelRecord c).1 else (labelRecord c).2
  record _ b := if b = 0 then (refRecord false).1 else (refRecord false).2
  live_sector _ := rfl
  live_position _ := rfl
  record_sector _ := rfl
  record_position _ := rfl

/-- One encounter state: site 0 has the candidate arrivals, requests
`(true,true)`, and exchange fires under either rule.  Other sites are vacuum. -/
def encounterState (either : Bool) (live record : Bool) : RingReceiver.State 3 :=
  (0, (fun _ => (true, true), (fun _ => false,
    fun x => if x = 2 then (live, false)
      else if x = 1 then (false, record) else (false, false))))

theorem encounterState_arrivals (either live record : Bool) :
    RingReceiver.arrivals (encounterState either live record).2.2.2 0 = (live, record) := by
  cases live <;> cases record <;>
    simp [encounterState, RingReceiver.arrivals, PMAction.OpenReferenceFlow.streamShift] <;>
    decide +kernel

theorem encounterState_exchange (either live record : Bool) :
    RingReceiver.exchange either ((encounterState either live record).2.1 0) = true := by
  simp [encounterState, RingReceiver.exchange]

/-- The encounter flag, evaluated by `receiver_flag_eq`. -/
theorem encounter_flag (either live record : Bool) :
    RingReceiver.receiverFlag either (encounterState either live record) 0 =
      if live ≠ record then 1 else 0 := by
  rw [RingReceiver.receiver_flag_eq, encounterState_arrivals, encounterState_exchange]
  simp

/-- Task H Step 3(a): the two record-port encounters for a label reproduce
the EP bitToll row.  Candidate identification, hypothesis. -/
theorem identification_flag_total (ident : RecordPortIdentification)
    (either : Bool) (c : Channels) :
    (∑ b : Fin 2,
      RingReceiver.receiverFlag either
        (encounterState either (ident.live c b) (ident.record c b)) 0) =
      WireSchedule.bitToll ident.reference c := by
  rw [Fin.sum_univ_two, encounter_flag, encounter_flag]
  rw [ident.live_sector, ident.live_position, ident.record_sector, ident.record_position]
  rw [bitToll_eq_hamming]
  unfold hamming refRecord
  cases ident.reference <;>
    cases h1 : (labelRecord c).1 <;> cases h2 : (labelRecord c).2 <;>
      norm_num [h1, h2]

/-- Task H Step 3(b): the general record bookkeeping identity holds on the
encounter state. -/
theorem identification_record_identity (ident : RecordPortIdentification)
    (either : Bool) (c : Channels) (b : Fin 2) :
    recordOccInt ((RingReceiver.tick 3 either
        (encounterState either (ident.live c b) (ident.record c b))).2.2.2) =
      recordOccInt (encounterState either (ident.live c b) (ident.record c b)).2.2.2 +
        (∑ x, upTerm (RingReceiver.exchange either
          ((encounterState either (ident.live c b) (ident.record c b)).2.1 x))
          (RingReceiver.arrivals
            (encounterState either (ident.live c b) (ident.record c b)).2.2.2 x)) -
        (∑ x, downTerm (RingReceiver.exchange either
          ((encounterState either (ident.live c b) (ident.record c b)).2.1 x))
          (RingReceiver.arrivals
            (encounterState either (ident.live c b) (ident.record c b)).2.2.2 x)) :=
  record_step_identity 3 either _

end PMElementaryParticles.IsolatedExcitation
