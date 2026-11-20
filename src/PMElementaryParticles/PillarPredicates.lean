import PMElementaryParticles.Protocol
import PersistenceMechanics.Requirements

/-!
# Weakest pillar predicates on finite protocols

The definitions and failure modes are from
`PM/paper/2_architecture_of_persistence.tex`, sections “The Six Pillars” and
“Necessity: Counterfactual Failure Modes”.  Each predicate below is the
weakest machine condition that rules out that failure mode.  Where the paper
allows more than one reading, each variant is named.

No physical quantity is added: all predicates use the finite `Protocol` data
and the certified bit-ring counters.
-/

noncomputable section
namespace PMElementaryParticles.PillarPredicates

open PMElementaryParticles.Protocol
open PMElementaryParticles.IsolatedExcitation
open PMElementaryParticles.HeavyFlipControl
open PMTransport
open PMTransport.RingReceiver

/-- Number of firing sites on one record-bit ring. -/
def firingCount (p : Protocol) (b : Fin 2) : ℕ :=
  ∑ x : Fin 3, if p.firing b x then 1 else 0

def totalFiringCount (p : Protocol) : ℕ :=
  ∑ b : Fin 2, firingCount p b

/-- Integer receiver Toll used by the finite enumeration. -/
def tollCount (p : Protocol) : ℕ :=
  ∑ b : Fin 2,
    if p.phase b then
      if bitDiffers p b then patternSum (p.firing b) p.x0 else 0
    else 0

theorem receiverToll_eq_tollCount (p : Protocol) :
    receiverToll p = (tollCount p : ℝ) := by
  unfold receiverToll tollCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : p.phase b <;> by_cases hd : bitDiffers p b <;> simp [hp, hd]

/-- Capacity: the finite label set plus a period capacity bound. -/
def capacity (p : Protocol) : Prop :=
  tollCount p ≤ 2 * 43

theorem capacity_realizes_finiteness :
    PersistenceMechanics.Requirements.Pillar.requirement
      PersistenceMechanics.Requirements.Pillar.capacity =
      PersistenceMechanics.Requirements.Requirement.finiteness := rfl

/-- Margin variant: no ring registers at every site. -/
def marginPerRing (p : Protocol) : Prop :=
  ∀ b : Fin 2, firingCount p b < 3

/-- Margin variant: the two rings do not jointly fill every site. -/
def marginTotal (p : Protocol) : Prop :=
  totalFiringCount p < 6

theorem margin_realizes_finiteness :
    PersistenceMechanics.Requirements.Pillar.requirement
      PersistenceMechanics.Requirements.Pillar.margin =
      PersistenceMechanics.Requirements.Requirement.finiteness := rfl

/-- Map variant: at least one record bit differs from the reference. -/
def mapAtLeastOne (p : Protocol) : Prop :=
  1 ≤ hamming (labelRecord p.label) (refRecord p.reference)

/-- Map variant: both record bits differ from the reference. -/
def mapBoth (p : Protocol) : Prop :=
  hamming (labelRecord p.label) (refRecord p.reference) = 2

theorem map_realizes_conservation :
    PersistenceMechanics.Requirements.Pillar.requirement
      PersistenceMechanics.Requirements.Pillar.map =
      PersistenceMechanics.Requirements.Requirement.conservation := rfl

/-- Protocol: the machine tick is reversible and both bit rings use the same
3-site clock.  The two facts are the certified `tick_bijective` and the common
`Fin 3` index.  The predicate is therefore the weakest one: `True` on the
finite data, with the two conservation facts supplied by the machine. -/
def protocolPillar (_p : Protocol) : Prop := True

instance protocolPillar_decidable (p : Protocol) : Decidable (protocolPillar p) :=
  isTrue trivial

theorem protocol_realizes_conservation :
    PersistenceMechanics.Requirements.Pillar.requirement
      PersistenceMechanics.Requirements.Pillar.protocol =
      PersistenceMechanics.Requirements.Requirement.conservation := rfl

/-- Toll variant: at least one registration in the period. -/
def tollTotal (p : Protocol) : Prop :=
  1 ≤ tollCount p

/-- Toll variant: every differing bit ring registers at least once. -/
def tollPerRing (p : Protocol) : Prop :=
  ∀ b : Fin 2, bitDiffers p b → 1 ≤
    (if p.phase b then patternSum (p.firing b) p.x0 else 0)

theorem toll_realizes_causality :
    PersistenceMechanics.Requirements.Pillar.requirement
      PersistenceMechanics.Requirements.Pillar.toll =
      PersistenceMechanics.Requirements.Requirement.causality := rfl

/-- Governor: the firing set is a proper subset, so not every transition is
allowed. -/
def governorProper (p : Protocol) : Prop :=
  ∃ b : Fin 2, ∃ x : Fin 3, p.firing b x = false

theorem governor_realizes_causality :
    PersistenceMechanics.Requirements.Pillar.requirement
      PersistenceMechanics.Requirements.Pillar.governor =
      PersistenceMechanics.Requirements.Requirement.causality := rfl

/-- Variant choices for the three pillars with more than one paper reading. -/
structure Variant where
  marginPerRing : Bool
  mapBoth : Bool
  tollPerRing : Bool

def Variants : List Variant :=
  [false, true].flatMap fun m =>
    [false, true].flatMap fun d =>
      [false, true].map fun t => ⟨m, d, t⟩

def margin (v : Variant) (p : Protocol) : Prop :=
  if v.marginPerRing then marginPerRing p else marginTotal p

def mapPredicate (v : Variant) (p : Protocol) : Prop :=
  if v.mapBoth then mapBoth p else mapAtLeastOne p

def toll (v : Variant) (p : Protocol) : Prop :=
  if v.tollPerRing then tollPerRing p else tollTotal p

def capacityBool (p : Protocol) : Bool := decide (tollCount p ≤ 2 * 43)

def marginBool (v : Variant) (p : Protocol) : Bool :=
  if v.marginPerRing then
    decide (firingCount p 0 < 3) && decide (firingCount p 1 < 3)
  else decide (totalFiringCount p < 6)

def mapBool (v : Variant) (p : Protocol) : Bool :=
  if v.mapBoth then decide (hamming (labelRecord p.label) (refRecord p.reference) = 2)
  else decide (1 ≤ hamming (labelRecord p.label) (refRecord p.reference))

def bitTollBool (p : Protocol) (b : Fin 2) : Bool :=
  if p.phase b then decide (1 ≤ patternSum (p.firing b) p.x0) else false

def tollBool (v : Variant) (p : Protocol) : Bool :=
  if v.tollPerRing then
    (!bitDiffers p 0 || bitTollBool p 0) && (!bitDiffers p 1 || bitTollBool p 1)
  else decide (1 ≤ tollCount p)

def allFiring (p : Protocol) : Bool :=
  p.firing 0 0 && p.firing 0 1 && p.firing 0 2 &&
    p.firing 1 0 && p.firing 1 1 && p.firing 1 2

def governorBool (p : Protocol) : Bool := !allFiring p

def satisfiesBool (v : Variant) (p : Protocol) : Bool :=
  capacityBool p && marginBool v p && mapBool v p && true && tollBool v p &&
    governorBool p

def satisfies (v : Variant) (p : Protocol) : Prop :=
  satisfiesBool v p = true

def survivors (v : Variant) : Finset Protocol :=
  allProtocols.filter (fun p => satisfiesBool v p)

theorem survivors_mem_iff (v : Variant) (p : Protocol) :
    p ∈ survivors v ↔ satisfies v p := by
  simp [survivors, satisfies, allProtocols]

end PMElementaryParticles.PillarPredicates
