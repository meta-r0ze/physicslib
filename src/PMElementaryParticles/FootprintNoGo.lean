import PMElementaryParticles.EPLabelGen

/-!
# Limits of footprints built from preserving root steps

A zero-key step keeps the glue generation. Every nonzero-key step changes it.
Among the 240 roots, those that also keep internal content are exactly the
24 roots of the aligned spacetime D4. This statement does not depend on a
channel, a generation, or the initial lattice position.

`reachableWithin` records relative displacements of words of at most a supplied
number of root steps. An arbitrary common functional of this set cannot separate
generations. It need not be a count or a physical footprint. The result does not
identify such a functional with `OccupancyCost.Footprint.events`. It does not
remove other program inputs: requests, timing, occupied state and admission.
Absolute sets translated by different initial positions are not identified.
-/

namespace PMElementaryParticles.FootprintNoGo
open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment
open PMElementaryParticles.EPLabel PMElementaryParticles.EPLabelGen
open PMElementaryParticles.EPSpine PMConstants.PacketGaugeActions

/-- The key test holds for all lattice increments, not only roots. -/
theorem generation_preserved_iff (z r : V) :
    glueKey (z + r) = glueKey z ↔ glueKey r = 0 := by
  rw [glueKey_add, add_eq_left]

theorem zero_key_preserves (z r : V) (h : glueKey r = 0) :
    glueKey (z + r) = glueKey z := (generation_preserved_iff z r).2 h

theorem nonzero_key_changes (z r : V) (h : glueKey r ≠ 0) :
    glueKey (z + r) ≠ glueKey z := mt (generation_preserved_iff z r).1 h

/-- Content preservation also depends only on the increment. -/
theorem content_preserved_iff (z r : V) :
    internalContent (z + r) = internalContent z ↔ internalContent r = 0 := by
  rw [internalContent_add, add_eq_left]

/-- Exhaustive classification in the existing aligned placement. -/
theorem preserving_root_iff : ∀ r ∈ rootList,
    (glueKey r = 0 ∧ internalContent r = 0) ↔ r ∈ spacetimeRoots := by
  decide +kernel

/-- This is the same root set at every generation and every label. -/
theorem step_preserves_both_iff (z r : V) (hr : r ∈ rootList) :
    (glueKey (z + r) = glueKey z ∧ internalContent (z + r) = internalContent z) ↔
      r ∈ spacetimeRoots := by
  rw [generation_preserved_iff, content_preserved_iff]
  exact preserving_root_iff r hr

/-- The finite list covers every norm-two lattice root, by the upstream completeness theorem. -/
theorem norm_two_preserves_both_iff (z r : V)
    (hr : PMSubstrate.Lattices.pairing r r = 2) :
    (glueKey (z + r) = glueKey z ∧ internalContent (z + r) = internalContent z) ↔
      r ∈ spacetimeRoots := step_preserves_both_iff z r (rootList_complete r hr)

/-- Preserving increments at a generation's placed channel. -/
def singleSteps (g : Generation) (c : Channels) : List V :=
  rootList.filter fun r =>
    g.1 + glueKey r = g.1 ∧
      internalContent (channelE8Gen (genIndex g) c + r) =
        internalContent (channelE8Gen (genIndex g) c)

theorem singleSteps_eq (g : Generation) (c : Channels) :
    singleSteps g c = spacetimeRoots := by
  apply List.filter_congr
  intro r hr
  simp only [decide_eq_decide]
  rw [add_eq_left, content_preserved_iff]
  exact (preserving_root_iff r hr).trans (by simp [spacetimeRoots, hr])

/-- All relative displacements reachable within the supplied event budget. -/
def reachableWithin (ticks : ℕ) (g : Generation) (c : Channels) : Set V :=
  {d | ∃ w : List V, w.length ≤ ticks ∧ (∀ r ∈ w, r ∈ singleSteps g c) ∧ w.sum = d}

theorem reachableWithin_independent (ticks : ℕ) (g h : Generation) (c d : Channels) :
    reachableWithin ticks g c = reachableWithin ticks h d := by
  simp only [reachableWithin, singleSteps_eq]

/-- No common functional of these reachable displacements can separate generations. -/
theorem footprint_functional_independent {A : Type*} (read : Set V → A)
    (ticks : ℕ) (g h : Generation) (c d : Channels) :
    read (reachableWithin ticks g c) = read (reachableWithin ticks h d) := by
  rw [reachableWithin_independent ticks g h c d]

/-- Keep the step index instead of collapsing all visits to one spatial support.
The window has step indices 0 through period - 1. This is a set of possible
relative events, not a selected execution or a multiplicity ledger. -/
def reachableEvents (period : ℕ) (g : Generation) (c : Channels) : Set (ℕ × V) :=
  {x | x.1 < period ∧ ∃ w : List V, w.length = x.1 ∧
    (∀ r ∈ w, r ∈ singleSteps g c) ∧ w.sum = x.2}

theorem reachableEvents_independent (period : ℕ) (g h : Generation) (c d : Channels) :
    reachableEvents period g c = reachableEvents period h d := by
  simp only [reachableEvents, singleSteps_eq]

/-- Keeping event positions and step indices still supplies no generation dependence. -/
theorem event_footprint_functional_independent {A : Type*} (read : Set (ℕ × V) → A)
    (period : ℕ) (g h : Generation) (c d : Channels) :
    read (reachableEvents period g c) = read (reachableEvents period h d) := by
  rw [reachableEvents_independent period g h c d]

end PMElementaryParticles.FootprintNoGo
