import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# PM requirements, the six pillars, and the substrate-postulate map

Persistence Mechanics rests on **three requirements** for any persistent system —
Finiteness, Conservation, Causality — realized through **six pillars**. This module names
those first-class, so the rest of the tree can say *what it is conditional on* in PM's own
terms.

The point of this framing: the postulates written down for the vacuum are **PM readings, not
assumptions about a substrate**. The flow is

> PM requirements → (readings) → postulates → **the substrate is derived**.

So the E8 lattice is a *conclusion* (`PMSubstrate.Main.persistence_selects`), not a premise.
Each postulate reading is certified against the actual substrate theorem in
`PMSubstrate.RequirementMap` (`Consequence` / `consequence_holds`), which also proves the reading
`Geometric → PMRequirements` (`geometric_reading`) and names the one open implication
(`S1_residual`). Here we name the requirements, the pillars, and the readings.

The three requirements are also stated abstractly (`PMRequirements`), with the framework
consequence that Conservation + Causality is reversibility.
-/

namespace PersistenceMechanics.Requirements

/-- **PM's three requirements** for any persistent system. -/
inductive Requirement
  /-- Bounded resources: bounded-cost sets of states are finite. -/
  | finiteness
  /-- Preserved identity-defining distinctions: the update never merges two states. -/
  | conservation
  /-- Well-ordered evolution: every state has a well-defined history. -/
  | causality
  deriving DecidableEq, Repr

instance : Fintype Requirement where
  elems := {Requirement.finiteness, Requirement.conservation, Requirement.causality}
  complete := by intro x; cases x <;> simp

/-- The **six pillars** through which the requirements are realized. -/
inductive Pillar
  | capacity
  | map
  | protocol
  | governor
  | toll
  | margin
  deriving DecidableEq, Repr

instance : Fintype Pillar where
  elems := {Pillar.capacity, Pillar.map, Pillar.protocol, Pillar.governor, Pillar.toll, Pillar.margin}
  complete := by intro x; cases x <;> simp

/-- Each pillar realizes one requirement: Capacity and Margin realize Finiteness, Map and
Protocol realize Conservation, Toll and Governor realize Causality. -/
def Pillar.requirement : Pillar → Requirement
  | .capacity => .finiteness
  | .margin => .finiteness
  | .map => .conservation
  | .protocol => .conservation
  | .toll => .causality
  | .governor => .causality

/-- A pillar *regulates* when its PM definition is an action on other transitions: Protocol
"coordinates state transitions", Governor "restricts which transitions the system can undergo".
The other four provision (Capacity, Margin, Map) or spend (Toll) on their own. -/
def Pillar.regulates : Pillar → Bool
  | .protocol => true
  | .governor => true
  | _ => false

/-- Sign of a pillar's term: removed transitions count `−1`, provisioned or spent `+1`. -/
def Pillar.sign (p : Pillar) : ℤ := if p.regulates then -1 else 1

/-- Exactly Protocol and Governor enter negatively — one regulator each for Conservation
(Map, Protocol) and Causality (Toll, Governor); Finiteness (Capacity, Margin) has none. -/
theorem Pillar.signs :
    Pillar.capacity.sign = 1 ∧ Pillar.margin.sign = 1 ∧ Pillar.map.sign = 1 ∧
      Pillar.toll.sign = 1 ∧ Pillar.protocol.sign = -1 ∧ Pillar.governor.sign = -1 := by decide

/-- Every requirement is realized by **exactly two** pillars — the six pillars are `3 × 2`. -/
theorem Pillar.fiber_card (r : Requirement) :
    (Finset.univ.filter (fun p : Pillar => Pillar.requirement p = r)).card = 2 := by
  cases r <;> decide

/-- Every requirement is realized. -/
theorem Pillar.requirement_surjective : Function.Surjective Pillar.requirement :=
  fun r => by cases r <;> decide

/-- **The PM requirements, abstractly.** A state type with an update and a real cost, satisfying
Finiteness (bounded-cost sets finite), Conservation (the update never merges states) and Causality
(every state has a well-defined history: the update is onto). This is PM's content; no substrate is
assumed. -/
structure PMRequirements (S : Type*) where
  /-- The update: one tick. -/
  step : S → S
  /-- The configuration cost. -/
  cost : S → ℝ
  finiteness : ∀ c : ℝ, {s : S | cost s ≤ c}.Finite
  conservation : Function.Injective step
  causality : Function.Surjective step

/-- **Conservation + Causality = reversibility.** An update that never merges states and reaches
every state is a bijection: the system evolves by a permutation, so identity is preserved in both
directions. (The lattice instance is `PMSubstrate.never_merge_iff_bijective`.) -/
theorem PMRequirements.bijective {S : Type*} (r : PMRequirements S) : Function.Bijective r.step :=
  ⟨r.conservation, r.causality⟩

/-- **The substrate postulates**, named as the PM readings they formalize. -/
inductive Postulate
  /-- Addresses form a full-rank lattice with integral symmetric cost. -/
  | addresses
  /-- Bounded-cost sets are finite. -/
  | finiteLevels
  /-- One-bit distinctions are readable by the substrate itself. -/
  | readable
  /-- Glue elements are bits (`2Λ* ⊆ Λ`). -/
  | bitAddressed
  /-- A nontrivial exchange law exists in which zero-pairing operations commute. -/
  | exchange
  /-- Least rank among such substrates (Economy). -/
  | economy
  /-- Two orthogonal irreducible bit-addressed rank-four root sectors. -/
  | sectors
  /-- The clock is a nondegenerate substrate plane; states are its discriminant group. -/
  | clockPlane
  /-- The schedule is reconstructable from gap-only local observations. -/
  | clockSchedule
  /-- The coordinate volume element squares to `−1`. -/
  | signature
  /-- The defect boundary has least topological complexity. -/
  | boundary
  deriving DecidableEq, Repr

instance : Fintype Postulate where
  elems := {Postulate.addresses, Postulate.finiteLevels, Postulate.readable, Postulate.bitAddressed,
    Postulate.exchange, Postulate.economy, Postulate.sectors, Postulate.clockPlane,
    Postulate.clockSchedule, Postulate.signature, Postulate.boundary}
  complete := by intro x; cases x <;> simp

/-- The primary PM requirement each postulate reading formalizes. -/
def Postulate.requirement : Postulate → Requirement
  | .addresses | .finiteLevels => .finiteness
  | .readable | .bitAddressed | .sectors | .clockPlane | .signature => .conservation
  | .exchange | .clockSchedule => .causality
  | .economy | .boundary => .finiteness

/-- Whether a reading additionally invokes PM's **Selection Principle** (least cost / Economy),
which is how ties between admissible structures are broken. -/
def Postulate.usesSelection : Postulate → Bool
  | .economy | .boundary => true
  | _ => false

/-- Every PM requirement is formalized by at least one reading. -/
theorem requirements_realized : ∀ r : Requirement, ∃ p : Postulate, Postulate.requirement p = r := by
  intro r; cases r <;> decide

end PersistenceMechanics.Requirements
