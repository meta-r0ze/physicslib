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

/-- Convert a start tick to a period and a phase, from the supplied clock origin. -/
def periodPhase {ticks : ℕ} (start : Fin ticks) : ℕ × ℕ :=
  (start.val / PMSubstrate.E8Values.Delta, start.val % PMSubstrate.E8Values.Delta)

/-- Last exclusive end of a booked block, measured from the clock origin. -/
def finishTick {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) : ℕ :=
  Finset.univ.sup fun e =>
    match s.2 e with
    | none => 0
    | some x => x.1.val + duration p e

def periods {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks) : ℕ :=
  (finishTick p s + PMSubstrate.E8Values.Delta - 1) / PMSubstrate.E8Values.Delta

theorem finishTick_le_horizon {ticks : ℕ} (p : Premises ticks) (s : Schedule ticks)
    (hs : s ∈ family p) : finishTick p s ≤ ticks := by
  have h := (mem_family p s).1 hs
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have hall : ∀ e : Event, fitsEvent p s e = true := by tauto
  apply Finset.sup_le
  intro e _
  have he := hall e
  cases hplace : s.2 e with
  | none => simp
  | some x =>
    simp only [fitsEvent, hplace, Bool.and_eq_true, decide_eq_true_eq] at he
    tauto

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

noncomputable section
open PMConstants.PacketGaugeActions ProtocolToll
open PMAction DiagonalReadout TollAmplitude

/-- Exact minima once the physical scalar cost is supplied. -/
def minima {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ) :
    Finset (Schedule ticks) := by
  classical
  exact (family p).filter (fun s => ∀ t ∈ family p, cost s ≤ cost t)

theorem mem_minima {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    (s : Schedule ticks) :
    s ∈ minima p cost ↔ s ∈ family p ∧ ∀ t ∈ family p, cost s ≤ cost t := by
  classical
  simp [minima]

theorem minima_nonempty {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    (h : (family p).Nonempty) : (minima p cost).Nonempty := by
  obtain ⟨s, hs, hmin⟩ := (family p).exists_min_image cost h
  exact ⟨s, (mem_minima p cost s).2 ⟨hs, hmin⟩⟩

/-- Economy picks precisely the maximal survival schedules inside the supplied family. -/
theorem best_survival_iff {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    (s : Schedule ticks) (β baseline : ℝ) (hβ : 0 < β) :
    (s ∈ family p ∧ ∀ t ∈ family p,
      Real.exp (-β * (baseline + cost t)) ≤ Real.exp (-β * (baseline + cost s))) ↔
      s ∈ minima p cost := by
  rw [mem_minima]
  exact PersistenceSelection.within_family_iff_cheapest β hβ cost (↑(family p)) baseline s

theorem tied_minimum {ticks : ℕ} (p : Premises ticks) (cost : Schedule ticks → ℝ)
    {s t : Schedule ticks} (hs : s ∈ minima p cost) (ht : t ∈ family p)
    (heq : cost t = cost s) : t ∈ minima p cost := by
  exact (mem_minima p cost t).2 ⟨ht, fun u hu =>
    heq.trans_le (((mem_minima p cost s).1 hs).2 u hu)⟩

/-- The observable two-visit subtotal when both electric record flags are paid. -/
def bitToll (colourReference : Bool) (c : Channels) : ℝ :=
  flag (3 * Real.pi * ElectricHeavyRecord.q c) +
    flag (3 * Real.pi / 2 * ElectricHeavyRecord.sectorDifference colourReference c)

/-- In the record-only account, the finite sum is exactly the two write flags. -/
theorem knownToll_recordOnly {ticks : ℕ} (b : Bool) (c : Channels) (s : Schedule ticks)
    (hp : paid s .position = true) (hs : paid s .sector = true)
    (ho : ∀ e, e ≠ .position → e ≠ .sector → paid s e = false) :
    knownToll b c s = bitToll s.1 c := by
  classical
  unfold knownToll bitToll
  rw [← Finset.sum_subset (Finset.subset_univ ({.position, .sector} : Finset Event)) ?_]
  · rw [Finset.sum_pair (show Event.position ≠ Event.sector by decide)]
    simp [hp, hs, visitFlag]
  · intro e _ he
    have h : e ≠ Event.position ∧ e ≠ Event.sector := by simpa using he
    simp [ho e h.1 h.2]

theorem colour_tolls (a : Fin 3) :
    bitToll true electronStatic = 2 ∧ bitToll true (upStatic a) = 0 ∧
      bitToll true (downStatic a) = 1 := by
  obtain ⟨he, hd, hu, -⟩ := HeavyFlipRecords.orbit_record_tolls a
  simpa only [bitToll, ElectricHeavyRecord.colour_reference_toll] using
    (show HeavyFlipRecords.orbitRecordToll electronStatic = 2 ∧
        HeavyFlipRecords.orbitRecordToll (upStatic a) = 0 ∧
        HeavyFlipRecords.orbitRecordToll (downStatic a) = 1 from ⟨he, hu, hd⟩)

theorem lepton_tolls (a : Fin 3) :
    bitToll false electronStatic = 1 ∧ bitToll false (upStatic a) = 1 ∧
      bitToll false (downStatic a) = 2 := by
  obtain ⟨he, hd, hu, -⟩ := ElectricHeavyRecord.lepton_reference_toll a
  exact ⟨he, hu, hd⟩

/-- Neither polarity weakly improves the known cost for every charged label. -/
theorem polarity_tradeoff (a : Fin 3) :
    bitToll false electronStatic < bitToll true electronStatic ∧
      bitToll true (upStatic a) < bitToll false (upStatic a) ∧
      bitToll true (downStatic a) < bitToll false (downStatic a) := by
  obtain ⟨he, hu, hd⟩ := colour_tolls a
  obtain ⟨he', hu', hd'⟩ := lepton_tolls a
  rw [he, hu, hd, he', hu', hd']
  norm_num

/-- For a common schedule, weights on the three charged labels must be supplied.
The remainder here includes all other contributions to the scalar objective. -/
def polarityCost (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) (pol : Bool) : ℝ :=
  we * bitToll pol electronStatic + wu * bitToll pol (upStatic a) +
    wd * bitToll pol (downStatic a) + remainder pol

/-- Exact threshold when the only candidates differ by sector-reference polarity
and the two output flags are charged in both. -/
theorem polarity_cost_difference (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) :
    polarityCost a we wu wd remainder true - polarityCost a we wu wd remainder false =
      we - wu - wd + (remainder true - remainder false) := by
  obtain ⟨he, hu, hd⟩ := colour_tolls a
  obtain ⟨he', hu', hd'⟩ := lepton_tolls a
  simp only [polarityCost, he, hu, hd, he', hu', hd']
  ring

theorem polarity_minimum_iff (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) :
    (∀ pol, polarityCost a we wu wd remainder true ≤ polarityCost a we wu wd remainder pol) ↔
      we - wu - wd + (remainder true - remainder false) ≤ 0 := by
  rw [← polarity_cost_difference, sub_nonpos]
  constructor
  · exact fun h => h false
  · intro h pol
    cases pol
    · exact h
    · exact le_rfl

theorem polarity_tie_iff (a : Fin 3) (we wu wd : ℝ) (remainder : Bool → ℝ) :
    polarityCost a we wu wd remainder true = polarityCost a we wu wd remainder false ↔
      we - wu - wd + (remainder true - remainder false) = 0 := by
  rw [← polarity_cost_difference, sub_eq_zero]

end

end PMElementaryParticles.WireSchedule
