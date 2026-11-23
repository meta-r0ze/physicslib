import PMElementaryParticles.RingSurvivors
import PMElementaryParticles.ProgramClasses
import PersistenceMechanics.Requirements

/-!
# A running program for every visible class

A program on the 43-site clock ring is a label, a reference, one firing pattern
per record-bit ring, and a start site (`RingProgram`). The pillar conditions
on the physical ring:

| Pillar | Condition (`RingProgram`) |
| --- | --- |
| Capacity | total registrations per period at most `2·43` |
| Margin | every registering ring stays below `43` per period |
| Map | the record differs from the reference (`MapRecord`), and the label's class is visible to the substrate's observables (`MapClass`, `ProgramClasses`) |
| Protocol | the reversible tick (`RingReceiver.tick_bijective`); no condition on the data |
| Toll | every differing ring registers at least once per period |
| Governor | some site does not fire |

The witness (`witness c`) takes the least-Toll reference (`leastRef`: lepton
when the two record bits agree, colour when they differ; Hamming distance `1`
for every label, `leastRef_hamming`) and one firing site per ring. By
`RingRates.one_site_exact` each differing ring registers exactly once per
period. So every visible class has a program meeting all six pillars
(`visible_class_has_program`), at the least Toll (`witness_total`), and the
invisible class has none (`invisible_class_no_program`).
-/

noncomputable section

namespace PMElementaryParticles.ProgramWitness

open PMConstants.PacketGaugeActions
open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.RingRates
open PMElementaryParticles.RingSurvivors
open PMElementaryParticles.ProgramClasses

/-- A program on the 43-site clock ring. -/
structure RingProgram where
  label : Channels
  reference : Bool
  firing : Fin 2 → Fin 43 → IsolatedRequests
  x0 : Fin 43

/-- The record-bit ring `b` must register: the label bit differs from the reference bit. -/
def differs (p : RingProgram) (b : Fin 2) : Prop :=
  bitOf (labelRecord p.label) b ≠ bitOf (refRecord p.reference) b

/-- Registrations of ring `b` in one period. -/
def registrations (p : RingProgram) (b : Fin 2) : ℕ :=
  localizedSumN 43 true (p.firing b) p.x0 43

def Capacity (p : RingProgram) : Prop := registrations p 0 + registrations p 1 ≤ 2 * 43
def Margin (p : RingProgram) : Prop := ∀ b, differs p b → registrations p b < 43
def MapRecord (p : RingProgram) : Prop :=
  1 ≤ hamming (labelRecord p.label) (refRecord p.reference)
def MapClass (p : RingProgram) : Prop := classOf p.label ≠ 4
def Toll (p : RingProgram) : Prop := ∀ b, differs p b → 1 ≤ registrations p b
def Governor (p : RingProgram) : Prop :=
  ∃ b x, PMKAutomaton.RingReceiver.exchange true (p.firing b x) = false

/-- All six pillars (Protocol holds by the reversible tick). -/
def Pillars (p : RingProgram) : Prop :=
  Capacity p ∧ Margin p ∧ MapRecord p ∧ MapClass p ∧ Toll p ∧ Governor p

/-- Least-Toll reference: lepton (`false`) when the two record bits agree,
colour (`true`) when they differ. -/
def leastRef (c : Channels) : Bool := (labelRecord c).1 != (labelRecord c).2

theorem leastRef_hamming : ∀ c : Channels,
    hamming (labelRecord c) (refRecord (leastRef c)) = 1 := by
  decide

/-- The witness program: least-Toll reference, one firing site per ring. -/
def witness (c : Channels) : RingProgram := ⟨c, leastRef c, fun _ => oneFiringN 43 0, 0⟩

theorem witness_registrations (c : Channels) (b : Fin 2) :
    registrations (witness c) b = 1 :=
  one_site_exact true 0 0

theorem witness_governor (c : Channels) : Governor (witness c) := by
  refine ⟨0, 1, ?_⟩
  simp [witness, oneFiringN, PMKAutomaton.RingReceiver.exchange]

theorem witness_pillars (c : Channels) (hc : classOf c ≠ 4) : Pillars (witness c) := by
  refine ⟨?_, ?_, ?_, hc, ?_, witness_governor c⟩
  · unfold Capacity; rw [witness_registrations, witness_registrations]; norm_num
  · intro b _; rw [witness_registrations]; norm_num
  · unfold MapRecord; rw [show (witness c).label = c from rfl,
      show (witness c).reference = leastRef c from rfl, leastRef_hamming]
  · intro b _; rw [witness_registrations]

/-- **Every visible class has a running program that meets all six pillars.** -/
theorem visible_class_has_program (k : Fin 6) (hk : k ≠ 4) :
    ∃ p : RingProgram, classOf p.label = k ∧ Pillars p := by
  obtain ⟨c, rfl⟩ := classOf_surjective k
  exact ⟨witness c, rfl, witness_pillars c hk⟩

/-- **The invisible class has no program**: Map fails on every program with
that label. -/
theorem invisible_class_no_program (p : RingProgram) (h : classOf p.label = 4) :
    ¬ Pillars p := fun hp => hp.2.2.2.1 h

/-- The witness pays the least Toll: its total over the differing rings equals
the Hamming distance to the reference, `1`, the lower bound for every
Toll-admissible program (`RingSurvivors.ringTotal_ge_hamming`). -/
theorem witness_total (c : Channels) :
    ringTotal c (leastRef c) (fun _ => oneFiringN 43 0) 0 = 1 := by
  rw [ringTotal_oneSite c (leastRef c) (fun _ => 0) 0, leastRef_hamming]

/-! ## Each pillar and the requirement it realizes

The paper's map from pillars to the three requirements
(`PersistenceMechanics.Requirements.Pillar.requirement`): Capacity and Margin
realize finiteness, Map and Protocol realize conservation, Toll and Governor
realize causality. -/

open PersistenceMechanics.Requirements in
theorem capacity_realizes : Pillar.requirement Pillar.capacity = Requirement.finiteness := rfl
open PersistenceMechanics.Requirements in
theorem margin_realizes : Pillar.requirement Pillar.margin = Requirement.finiteness := rfl
open PersistenceMechanics.Requirements in
theorem map_realizes : Pillar.requirement Pillar.map = Requirement.conservation := rfl
open PersistenceMechanics.Requirements in
theorem protocol_realizes : Pillar.requirement Pillar.protocol = Requirement.conservation := rfl
open PersistenceMechanics.Requirements in
theorem toll_realizes : Pillar.requirement Pillar.toll = Requirement.causality := rfl
open PersistenceMechanics.Requirements in
theorem governor_realizes : Pillar.requirement Pillar.governor = Requirement.causality := rfl

end PMElementaryParticles.ProgramWitness

end
