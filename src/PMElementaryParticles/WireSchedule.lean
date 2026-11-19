import PMElementaryParticles.ElectricHeavyRecord
import PMElementaryParticles.ChargedInsertion
import PMElementaryParticles.ElectricCompanionSetupToll
import PMAction.PersistenceSelection

/-!
# Finite serial wire-cycle candidates

A bounded family for the literal Schur order with the exact two-visit
electric writer. It represents a cycle at one glue address. Other record
writers and simultaneous pulses would need different execution templates.
The finite search does not supply physical gate admission, tick calibration,
or a registration policy.
-/

namespace PMElementaryParticles.WireSchedule

/-- At most one occurrence of each block in this serial template. -/
inductive Event
  | staticFlip | gappedCrossing | referenceFlip | gluedCrossing
  | nodeEnter | nodeLeave | referenceRenewal
  | doublet | chargedCurrent | bankSetup | position | sector | recordExport
  | matchFirst | matchSecond | offset | vacancyProbe
  deriving DecidableEq

instance : Fintype Event :=
  Fintype.ofList [.staticFlip, .gappedCrossing, .referenceFlip, .gluedCrossing,
    .nodeEnter, .nodeLeave, .referenceRenewal, .doublet, .chargedCurrent,
    .bankSetup, .position, .sector, .recordExport, .matchFirst, .matchSecond,
    .offset, .vacancyProbe] (by intro e; cases e <;> simp)

 /-- Whole carrier word, retained plus port, minus port, or stored record. -/
inductive Branch
  | carrier | plus | minus | recorded
  deriving DecidableEq

instance : Fintype Branch :=
  Fintype.ofList [.carrier, .plus, .minus, .recorded] (by intro b; cases b <;> simp)

/-- Start, live branch and whether this visit is charged as a registration. -/
abbrev Placement (ticks : ℕ) := Fin ticks × Branch × Bool

/-- The first bit chooses the colour (true) or lepton (false) sector reference. -/
abbrev Schedule (ticks : ℕ) := Bool × (Event → Option (Placement ticks))

/-- All calibration and physical admission choices for this template.
The horizon is `ticks`. The admission predicate supplies phase availability,
record lifecycle, ownership of paid visits, and any further trigger constraints.
A fresh record in this template needs its writer in the same cycle. -/
structure Premises (ticks : ℕ) where
  address : Fin 3
  shortFlip : Bool
  quarterTicks : ℕ
  chargedCurrent : Bool
  otherTicks : Event → ℕ
  admits : Schedule ticks → Bool

/-- Flip budgets from the two certified beta words. The crossing budgets
assume serial principal half-pulses on their common root clock. -/
def duration {ticks : ℕ} (p : Premises ticks) : Event → ℕ
  | .staticFlip | .referenceFlip => (if p.shortFlip then 24 else 32) * p.quarterTicks
  | .gappedCrossing | .gluedCrossing => 12 * p.quarterTicks
  | e => p.otherTicks e

/-- Required work in the specified template. The route is from
`ReferenceClassHop` and `ReferenceNode`. The optional charged-current event
needs its position bit (`EventRequirements.pairs_of_sign`). The fresh heavy
record uses both electric visits. The offset uses the two matched tests at
address two (`ChargedInsertion.joint_selector`, `select_static`). -/
def required {ticks : ℕ} (p : Premises ticks) : Event → Bool
  | .staticFlip | .gappedCrossing => true
  | .referenceFlip | .position | .sector => p.address == 0
  | .nodeEnter | .nodeLeave => p.address != 0
  | .doublet | .chargedCurrent => p.chargedCurrent
  | .matchFirst | .matchSecond | .offset => p.address == 2
  | _ => false

/-- These are circuit ports in the specified implementation. The heavy
flip's identification with a record-controlled insertion is a premise.
The doublet comparison writes a bit whose two values may both be used,
so its control port is represented by the stored record. -/
def branchAllowed : Event → Branch → Bool
  | .staticFlip, .carrier | .gappedCrossing, .carrier => true
  | .referenceFlip, .recorded | .gluedCrossing, .recorded => true
  | .position, .recorded | .sector, .recorded => true
  | .doublet, .recorded | .chargedCurrent, .recorded => true
  | .matchFirst, .plus | .matchSecond, .plus | .offset, .recorded => true
  | .nodeEnter, _ | .nodeLeave, _ | .referenceRenewal, _ => true
  | .bankSetup, _ | .recordExport, _ | .vacancyProbe, _ => true
  | _, _ => false

/-- Prerequisites of each present event. The static/crossing/reference
chronology is the literal Schur-order premise. The fresh heavy writer
uses the position result to choose the sector reference. -/
def predecessors : Event → List Event
  | .gappedCrossing => [.staticFlip]
  | .referenceFlip => [.gappedCrossing, .sector]
  | .gluedCrossing => [.sector]
  | .nodeEnter => [.gappedCrossing]
  | .nodeLeave => [.nodeEnter]
  | .chargedCurrent => [.doublet]
  | .sector => [.position]
  | .matchSecond => [.matchFirst]
  | .offset => [.matchSecond]
  | _ => []

def endsBefore {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) (a b : Event) : Bool :=
  match s.2 a, s.2 b with
  | some x, some y => decide (x.1.val + duration p a ≤ y.1.val)
  | _, _ => false

/-- Optional events may be omitted on their route but cannot use the wrong address. -/
def allowed {ticks : ℕ} (p : Premises ticks) : Event → Bool
  | .gluedCrossing | .bankSetup | .recordExport => p.address == 0
  | .referenceRenewal | .vacancyProbe => true
  | e => required p e

private def fitsEvent {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks)
    (e : Event) : Bool :=
  match s.2 e with
  | none => !required p e
  | some x =>
      allowed p e &&
      decide (0 < duration p e ∧ x.1.val + duration p e ≤ ticks) &&
      branchAllowed e x.2.1 &&
      (predecessors e).all (fun a => endsBefore p s a e) &&
      (e != .position || !(s.2 .bankSetup).isSome || endsBefore p s .bankSetup e) &&
      (e != .recordExport || [.referenceFlip, .gluedCrossing].all
        (fun a => !(s.2 a).isSome || endsBefore p s a e)) &&
      decide (∀ f : Event,
        (e == f || !(s.2 f).isSome || endsBefore p s e f || endsBefore p s f e) = true)

/-- Test the finite constraints. Optional setup precedes the writer if
present. Export is timed after every present consumer of the heavy record.
The admission premise checks that an omitted setup or export is viable. -/
def admissible {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) : Bool :=
  p.admits s &&
    decide (0 < p.quarterTicks) &&
    (p.shortFlip || p.quarterTicks % 2 == 0) &&
    decide (∀ e : Event, fitsEvent p s e = true)

/-- Computably enumerable for a supplied finite horizon and Boolean admission
test. Costs can be minimized on projections without iterating slot injections. -/
def family {ticks : ℕ} (p : Premises ticks) : Finset (Schedule ticks) :=
  Finset.univ.filter (fun s => admissible p s = true)

theorem mem_family {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) :
    s ∈ family p ↔ admissible p s = true := by
  simp [family]

noncomputable section
open PMConstants.PacketGaugeActions ProtocolInventory ProtocolToll
open PMAction DiagonalReadout InterferenceReadout TollAmplitude
open scoped BigOperators

/-- One account for each actual static label, with the opposite wall's
equal population when the visit reads a massive state. The two prep flags
are available only for the certified equal-slot companion setup. -/
def visitFlag (companionSetup colourReference : Bool) (c : Channels) : Event → Option ℝ
  | .position => some (flag (3 * Real.pi * ElectricHeavyRecord.q c))
  | .sector => some (flag (3 * Real.pi / 2 * ElectricHeavyRecord.sectorDifference colourReference c))
  | .doublet => some (EventRequirements.massiveFlag (3 * Real.pi / 2)
      (ControlledGluedRegister.opposite c) c)
  | .matchFirst => some (flagProbability (ChargedInsertion.matchedTransport (baseProtocol c)) c)
  | .matchSecond =>
      let U := ChargedInsertion.matchedTransport (baseProtocol c)
      some (flagProbability (U * U) c)
  | .vacancyProbe => some (hyperchargeFlag (3 * Real.pi / 4) c)
  | .bankSetup =>
      if companionSetup then some (((∑ j, ElectricCompanionSetupToll.visitFlag true j) +
        ∑ j, ElectricCompanionSetupToll.visitFlag false j) / 2) else none
  | _ => none

def paid {ticks : ℕ} (s : Schedule ticks) (e : Event) : Bool :=
  ((s.2 e).map (fun x => x.2.2)).getD false

/-- This is a subtotal. A visit with no proved flag contributes only to the
unpriced part of the account, even if the schedule marks it as paid. -/
def knownToll {ticks : ℕ} (companionSetup : Bool) (c : Channels) (s : Schedule ticks) : ℝ :=
  ∑ e, if paid s e then (visitFlag companionSetup s.1 c e).getD 0 else 0

def unpricedVisits {ticks : ℕ} (companionSetup : Bool) (c : Channels)
    (s : Schedule ticks) : Finset Event :=
  Finset.univ.filter (fun e => paid s e = true ∧ (visitFlag companionSetup s.1 c e).isNone = true)

/-- The explicit remainder pays the unpriced visits and any additional
preparation, primitive pulse, export, renewal and controller costs.
It must be supplied by a physical account. -/
def fullToll {ticks : ℕ} (companionSetup : Bool) (unpriced : Channels → Schedule ticks → ℝ)
    (c : Channels) (s : Schedule ticks) : ℝ :=
  knownToll companionSetup c s + unpriced c s

def amplitude {ticks : ℕ} (companionSetup : Bool) (unpriced : Channels → Schedule ticks → ℝ)
    (c : Channels) (s : Schedule ticks) : ℝ :=
  wireAmplitude (fullToll companionSetup unpriced c s)

theorem matched_flag_account (b pol : Bool) (c : Channels) (hc : active c = false) :
    visitFlag b pol c .matchFirst = some 0 ∧ visitFlag b pol c .matchSecond = some 0 := by
  obtain ⟨h₁, h₂⟩ := ChargedInsertion.matched_flags_zero (baseProtocol c) c hc rfl
  exact ⟨congrArg some h₁, congrArg some h₂⟩

theorem knownToll_eq_of_paid_eq {ticks : ℕ} (b : Bool) (c : Channels)
    {s t : Schedule ticks} (hp : s.1 = t.1) (h : ∀ e, paid s e = paid t e) :
    knownToll b c s = knownToll b c t := by
  simp [knownToll, hp, h]

end

end PMElementaryParticles.WireSchedule
