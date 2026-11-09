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
The `MapRow` table below records, for each postulate reading, the PM requirement it formalizes
and the Lean declaration in the substrate layer (`PMSubstrate`, necessarily downstream of this
framework module) that forces its consequence; coverage of every reading is machine-checked.

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

/-- One row of the **requirement ↔ postulate ↔ theorem** map: the reading, and the Lean
declaration that forces its consequence in the substrate layer. (Names are strings because that
layer is downstream of this framework module.) -/
structure MapRow where
  /-- The postulate reading. -/
  postulate : Postulate
  /-- The Lean declaration forcing the reading's consequence (in `PMSubstrate`). -/
  leanName : String
  /-- What it delivers. -/
  consequence : String
  deriving Repr

/-- The map from PM's requirements, through the postulate readings, to what the substrate layer
proves. Each row is one reading. -/
def map : List MapRow :=
  [ ⟨.addresses, "Vacuum.Substrate", "a lattice with integral symmetric cost A"⟩
  , ⟨.finiteLevels, "Vacuum.geometric_lattice / Translation.posDef_iff_finite_levels",
      "A positive definite"⟩
  , ⟨.readable, "Vacuum.geometric_lattice / SelfReadable.bitAddressed_bitReadable_unimodular",
      "det A odd; with bits, unimodular"⟩
  , ⟨.bitAddressed, "Vacuum.Geometric.bitAddressed", "involutive glue, 2Λ* ⊆ Λ"⟩
  , ⟨.exchange, "Vacuum.geometric_lattice / OrthogonalExchange.orthogonal_nontrivial_exchange_forces_even",
      "the lattice is even"⟩
  , ⟨.economy, "Vacuum.geometric_selects_e8 / economy_from_hazard",
      "rank 8, then E8"⟩
  , ⟨.sectors, "Vacuum.sectors_are_d4", "two D4 sectors, ν = 16, N = 32"⟩
  , ⟨.clockPlane, "Vacuum.vacuum_selects", "complex multiplication, Δ = |D|"⟩
  , ⟨.clockSchedule, "Vacuum.schedule_selects_43_of_reconstructible", "32 ≤ Δ ≤ 64, so Δ = 43"⟩
  , ⟨.signature, "Derived.one_time / DerivedParameters.signature_volume_square", "one time direction"⟩
  , ⟨.boundary, "Derived.boundary_sphere / Descartes.descartes", "S², χ = 2"⟩ ]

/-- The map covers every reading, exactly once. -/
theorem map_covers : (map.map MapRow.postulate).toFinset = Finset.univ ∧
    (map.map MapRow.postulate).Nodup := by decide

/-- Every PM requirement is formalized by at least one reading. -/
theorem requirements_realized : ∀ r : Requirement, ∃ p : Postulate, Postulate.requirement p = r := by
  intro r; cases r <;> decide

end PersistenceMechanics.Requirements
