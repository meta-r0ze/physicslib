import PMSubstrate.NetCost
import PMSubstrate.PersistenceEvents
import PMSubstrate.CapacityBarbier
import PersistenceMechanics.Requirements
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The index as net transitions per cycle

Every term is an expected number of transitions per cycle (`NetCost`), with one transition as the
unit (Closure). Provisioning pillars add transitions; regulating pillars remove them.

* **Capacity** — boundary transitions. The defect's identity is its distinctions from the vacuum
  (Conservation); a site all of whose neighbours share its state carries no distinction
  (`interior_carries_no_distinction`), so only the boundary costs. At speed one, refreshing one
  unit of boundary takes one tick, i.e. one transition. The ordered distinction count lists each
  boundary edge twice, so this is density `1/2` per ordered pair
  (`Distinctions.cost_per_cut_edge`). The largest causally admissible boundary
  is `πΔ` for any shape (`Capacity.capacity_is_max`).
* **Map** — `χ` boundary closures per cycle (unit weight).
* **Toll, Margin** — probabilities of a valid transition / one configuration (incurred, `+`).
* **Protocol, Governor** — probabilities of a transition removed by coordination / restriction
  (`−`, `NetCost.removal_subtracts`).
-/

noncomputable section
namespace PMSubstrate.NetIndex

/-- A distinction: neighbouring sites in different states. -/
def Distinction {V : Type*} (G : SimpleGraph V) (S : Set V) (u v : V) : Prop :=
  G.Adj u v ∧ (u ∈ S ↔ v ∉ S)

/-- Interior sites carry no distinction: only the boundary costs. -/
theorem interior_carries_no_distinction {V : Type*} (G : SimpleGraph V) (S : Set V) (u : V)
    (hu : u ∈ S) (hint : ∀ v, G.Adj u v → v ∈ S) : ∀ v, ¬ Distinction G S u v := by
  rintro v ⟨hadj, hd⟩
  exact (hd.mp hu) (hint v hadj)

/-- Vacuum sites (outside the defect, with only vacuum neighbours) carry none either. -/
theorem vacuum_carries_no_distinction {V : Type*} (G : SimpleGraph V) (S : Set V) (u : V)
    (hu : u ∉ S) (hext : ∀ v, G.Adj u v → v ∉ S) : ∀ v, ¬ Distinction G S u v := by
  rintro v ⟨hadj, hd⟩
  exact hext v hadj (by by_contra h; exact hu (hd.mpr h))

/-- **The index as net transitions per cycle.** Provisioning terms minus removed transitions, each
an expected count with unit toll, equals the six-term index on the forced parameters. -/
theorem index_as_net_transitions :
    impedance baseline =
      (capacityTerm baseline + mapTerm baseline + tollTerm baseline + marginTerm baseline) -
        ((1 : ℝ) / 167 + 2 / 43) := by
  have h := PersistenceEvents.corrections_as_probabilities
  obtain ⟨-, -, -, hp, hg, -⟩ := h
  unfold impedance
  linarith

end PMSubstrate.NetIndex
