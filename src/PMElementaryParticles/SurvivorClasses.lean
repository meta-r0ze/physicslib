import PMElementaryParticles.PillarPredicates

/-!
# Structural survivor classes for the pillar filter

The pillar predicates read only:

* `labelRecord c` (not the raw label),
* the reference record,
* the two firing patterns,
* the two phases,
* the packet site `x0`.

`Reduced` is that quotient.  Predicate evaluation is definitionally the same on
`Protocol` and on its reduced image.  The raw label multiplicity is the number
of labels sharing a record class.
-/

noncomputable section
set_option maxRecDepth 10000
namespace PMElementaryParticles.SurvivorClasses

open PMElementaryParticles.Protocol
open PMElementaryParticles.PillarPredicates
open PMElementaryParticles.HeavyFlipControl
open PMElementaryParticles.IsolatedExcitation

abbrev Pattern := Fin 3 → Bool
abbrev PatternPair := Fin 2 → Pattern

structure Reduced where
  record : Record
  reference : Bool
  firing : PatternPair
  phase : Fin 2 → Bool
  x0 : Fin 3

deriving instance DecidableEq for Reduced
deriving instance Fintype for Reduced

def ofProtocol (p : Protocol) : Reduced where
  record := labelRecord p.label
  reference := p.reference
  firing := p.firing
  phase := p.phase
  x0 := p.x0

def labelBitR (r : Reduced) (b : Fin 2) : Bool := bitOf r.record b
def referenceBitR (r : Reduced) (b : Fin 2) : Bool := bitOf (refRecord r.reference) b
def bitDiffersR (r : Reduced) (b : Fin 2) : Bool := labelBitR r b != referenceBitR r b

def firingCountR (r : Reduced) (b : Fin 2) : ℕ :=
  ∑ x : Fin 3, if r.firing b x then 1 else 0

def totalFiringCountR (r : Reduced) : ℕ := ∑ b : Fin 2, firingCountR r b

def tollCountR (r : Reduced) : ℕ :=
  ∑ b : Fin 2,
    if r.phase b then
      if bitDiffersR r b then patternSum (r.firing b) r.x0 else 0
    else 0

def capacityR (r : Reduced) : Bool := decide (tollCountR r ≤ 2 * 43)

def marginBoolR (v : Variant) (r : Reduced) : Bool :=
  if v.marginPerRing then
    decide (firingCountR r 0 < 3) && decide (firingCountR r 1 < 3)
  else decide (totalFiringCountR r < 6)

def mapBoolR (v : Variant) (r : Reduced) : Bool :=
  if v.mapBoth then decide (hamming r.record (refRecord r.reference) = 2)
  else decide (1 ≤ hamming r.record (refRecord r.reference))

def bitTollBoolR (r : Reduced) (b : Fin 2) : Bool :=
  if r.phase b then decide (1 ≤ patternSum (r.firing b) r.x0) else false

def tollBoolR (v : Variant) (r : Reduced) : Bool :=
  if v.tollPerRing then
    (!bitDiffersR r 0 || bitTollBoolR r 0) && (!bitDiffersR r 1 || bitTollBoolR r 1)
  else decide (1 ≤ tollCountR r)

def allFiringR (r : Reduced) : Bool :=
  r.firing 0 0 && r.firing 0 1 && r.firing 0 2 &&
    r.firing 1 0 && r.firing 1 1 && r.firing 1 2

def governorBoolR (r : Reduced) : Bool := !allFiringR r

def satisfiesBoolR (v : Variant) (r : Reduced) : Bool :=
  capacityR r && marginBoolR v r && mapBoolR v r && true && tollBoolR v r &&
    governorBoolR r

def SurvivorsR (v : Variant) : Finset Reduced :=
  Finset.univ.filter (fun r => satisfiesBoolR v r)

theorem satisfiesBool_eq (v : Variant) (p : Protocol) :
    satisfiesBool v p = satisfiesBoolR v (ofProtocol p) := by
  rfl

theorem tollCount_eq (p : Protocol) :
    tollCount p = tollCountR (ofProtocol p) := rfl

def labelMultiplicity (rec : Record) : ℕ :=
  (Finset.univ.filter fun c : PMConstants.PacketGaugeActions.Channels => labelRecord c = rec).card

/-- Labels sharing a record class are indistinguishable to every pillar
predicate when the other protocol fields agree. -/
theorem satisfies_labelRecord_invariant (v : Variant) (p q : Protocol)
    (hrec : labelRecord p.label = labelRecord q.label)
    (href : p.reference = q.reference) (hfire : p.firing = q.firing)
    (hphase : p.phase = q.phase) (hx : p.x0 = q.x0) :
    satisfies v p ↔ satisfies v q := by
  unfold satisfies
  rw [satisfiesBool_eq, satisfiesBool_eq]
  unfold ofProtocol
  rw [hrec, href, hfire, hphase, hx]

/-- Every predicate reads the reduced data only. -/
theorem survives_iff_reduced (v : Variant) (p : Protocol) :
    p ∈ survivors v ↔ ofProtocol p ∈ SurvivorsR v := by
  simp [survivors, SurvivorsR, satisfies, satisfiesBool_eq, allProtocols]

/-- The four defensible variants with the weakest Map condition. -/
def RobustVariants : List Variant :=
  [⟨false, false, false⟩, ⟨false, false, true⟩,
   ⟨true, false, false⟩, ⟨true, false, true⟩]

def RobustCore : Finset Reduced :=
  Finset.univ.filter fun r => RobustVariants.all (fun v => satisfiesBoolR v r)

theorem robust_core_eq :
    RobustCore = SurvivorsR ⟨true, false, true⟩ := by
  decide +kernel

theorem robust_core_card : RobustCore.card = 1224 := by
  decide +kernel

theorem survivorsR_cards :
    (SurvivorsR ⟨false, false, false⟩).card = 2352 ∧
    (SurvivorsR ⟨false, false, true⟩).card = 1608 ∧
    (SurvivorsR ⟨false, true, false⟩).card = 1032 ∧
    (SurvivorsR ⟨false, true, true⟩).card = 288 ∧
    (SurvivorsR ⟨true, false, false⟩).card = 1800 ∧
    (SurvivorsR ⟨true, false, true⟩).card = 1224 ∧
    (SurvivorsR ⟨true, true, false⟩).card = 792 ∧
    (SurvivorsR ⟨true, true, true⟩).card = 216 := by
  decide +kernel

end PMElementaryParticles.SurvivorClasses
