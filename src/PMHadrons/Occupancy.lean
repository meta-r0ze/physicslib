import PMHadrons.MesonMasses
import PersistenceMechanics.SelectionSymmetry
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Composite occupancy: the minimum room a persistent configuration holds

On E8 a composite is a cohort of elementary carriers placed on substrate cells. Its mass is the
**occupancy cost** `n · α⁻¹ + residual`, where `n` is the number of cells the persistent
configuration holds. This module makes the "minimum room" reading precise, all E8-native.

* `minOccupancy_le` / `not_persistent_of_card_lt` — the **minimum-room principle**: every
  persistent placement holds at least `n` cells, and a placement below `n` has nowhere to stand
  and is not persistent (it rearranges).
* `occupancyMass`, `pionPlus_eq_occupancyMass`, `kaonPlus_eq_occupancyMass` — the meson ledgers
  *are* the occupancy form `n · cellBudget + residual`.
* `two_le_length_of_colourNeutral` / `occupancy_ge_two_of_colourNeutral` — a colour-neutral
  composite needs at least two carriers, so under one cell per carrier it needs at least
  `χ = 2` cells. This derives the pion's occupancy **lower bound**; the kaon's extra `σ` is the
  remaining input (`REVIEW-AND-NEXT.md` item 1).
* `tied_minimal_of_moved` — a relabeling that preserves persistence and occupancy and moves a
  least-occupancy placement produces a *second* one, so occupancy alone does not select a
  placement and `n` stays an input until the persistence predicate forces a unique minimizer.

Standard-Model objects do not appear here.
-/

namespace PMHadrons.Occupancy

open Finset

/-- A placement of a carrier cohort: the finite set of substrate cells it holds. -/
abbrev Placement (Cell : Type*) := Finset Cell

/-- Occupancy: the number of cells held. -/
def occupancy (p : Placement Cell) : ℕ := p.card

variable {Cell : Type*} [Fintype Cell] [DecidableEq Cell]

/-- The occupancies of the persistent placements. -/
noncomputable def persistentOccupancies (P : Placement Cell → Prop) : Finset ℕ := by
  classical
  exact (univ.filter P).image occupancy

/-- **Minimum room.** The least occupancy among persistent placements. -/
noncomputable def minOccupancy (P : Placement Cell → Prop) (h : ∃ p, P p) : ℕ := by
  classical
  exact (persistentOccupancies P).min' (by
    obtain ⟨p, hp⟩ := h
    exact ⟨occupancy p, mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_univ p, hp⟩, rfl⟩⟩)

omit [DecidableEq Cell] in
/-- **Minimum-room principle.** Every persistent placement holds at least the minimum occupancy. -/
theorem minOccupancy_le {P : Placement Cell → Prop} (h : ∃ p, P p) {p : Placement Cell}
    (hp : P p) : minOccupancy P h ≤ occupancy p := by
  classical
  exact min'_le _ _ (mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_univ p, hp⟩, rfl⟩)

omit [DecidableEq Cell] in
/-- **Below the minimum room nothing persists.** A placement holding fewer than `n` cells cannot
be self-supporting, so it rearranges. -/
theorem not_persistent_of_card_lt {P : Placement Cell → Prop} (h : ∃ p, P p)
    {p : Placement Cell} (hlt : occupancy p < minOccupancy P h) : ¬ P p :=
  fun hp => absurd (lt_of_lt_of_le hlt (minOccupancy_le h hp)) (Nat.lt_irrefl _)

/-! ## The meson ledgers are the occupancy form -/

/-- The E8 mass of a composite of occupancy `n`: `n` six-pillar cell budgets plus the residual. -/
noncomputable def occupancyMass (n : ℕ) (residual : ℝ) : ℝ :=
  (n : ℝ) * PMHadrons.MesonMasses.cellBudget + residual

/-- The pion ledger is the occupancy form with `n = χ = 2`. -/
theorem pionPlus_eq_occupancyMass :
    PMHadrons.MesonMasses.pionPlus = occupancyMass 2 PMHadrons.MesonMasses.pionPlusResidual := by
  rw [PMHadrons.MesonMasses.pionPlus_cells]
  unfold occupancyMass PMHadrons.MesonMasses.pionCells
  rw [PMSubstrate.E8Values.chi_eq]

/-- The kaon ledger is the occupancy form with `n = σ + χ = 7`. -/
theorem kaonPlus_eq_occupancyMass :
    PMHadrons.CompositeMasses.kaonPlus =
      occupancyMass 7 PMHadrons.MesonMasses.kaonPlusResidual := by
  rw [PMHadrons.MesonMasses.kaonPlus_cells]
  unfold occupancyMass PMHadrons.MesonMasses.kaonCells
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq]
  norm_num

/-! ## Colour neutrality forces at least two carriers

A carrier carries one of the `σ − χ = 3` colours or its anticolour. A colour-neutral composite
must balance every colour against its anticolour, so a nonempty neutral cohort needs at least two
carriers. Under one cell per carrier, that is an occupancy lower bound of `χ = 2`. -/

/-- A carrier colour charge: one of the three colours, or its anticolour. -/
inductive ColourCharge where
  | colour (i : Fin 3)
  | anticolour (i : Fin 3)
  deriving DecidableEq, Repr

/-- Net colour content of a cohort on one colour type: colours minus anticolours. -/
def netColour (c : List ColourCharge) (i : Fin 3) : ℤ :=
  (c.filter (fun x => x = .colour i)).length - (c.filter (fun x => x = .anticolour i)).length

/-- A cohort is colour-neutral when every colour is balanced by its anticolour. -/
def ColourNeutral (c : List ColourCharge) : Prop := ∀ i, netColour c i = 0

/-- **A colour-neutral nonempty cohort has at least two carriers.** One carrier cannot balance its
own colour, so it is never neutral. -/
theorem two_le_length_of_colourNeutral {c : List ColourCharge}
    (h : ColourNeutral c) (hne : c ≠ []) : 2 ≤ c.length := by
  rcases Nat.lt_or_ge c.length 2 with hlt | hge
  · exfalso
    have h0 : c.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
    have h1 : c.length ≠ 1 := by
      intro h1
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h1
      cases x with
      | colour i => exact absurd (h i) (by simp [netColour])
      | anticolour i => exact absurd (h i) (by simp [netColour])
    omega
  · exact hge

omit [Fintype Cell] [DecidableEq Cell] in
/-- **Occupancy lower bound `χ`.** A colour-neutral nonempty cohort placed with one cell per
carrier holds at least `χ = 2` cells. -/
theorem occupancy_ge_two_of_colourNeutral {c : List ColourCharge} (h : ColourNeutral c)
    (hne : c ≠ []) (p : Placement Cell) (hp : c.length ≤ occupancy p) : 2 ≤ occupancy p :=
  le_trans (two_le_length_of_colourNeutral h hne) hp

/-! ## Derived or tied -/

omit [Fintype Cell] [DecidableEq Cell] in
/-- A relabeling that preserves the persistence predicate and the occupancy, applied to a
least-occupancy persistent placement, yields a *second* one. So the occupancy `n` has multiple
minimizers and no occupancy-only cost singles out a placement: `n` is derivable only when the
persistence predicate forces a **unique** minimizer (`SelectionSymmetry.unique_minimizer_fixed`),
and otherwise stays an input. -/
theorem tied_minimal_of_moved {P : Placement Cell → Prop} {σ : Placement Cell ≃ Placement Cell}
    (hP : ∀ p, P (σ p) ↔ P p) (hcard : ∀ p, occupancy (σ p) = occupancy p)
    {p : Placement Cell} (hp : P p) (hmove : σ p ≠ p) :
    σ p ≠ p ∧ P (σ p) ∧ occupancy (σ p) = occupancy p :=
  ⟨hmove, (hP p).mpr hp, hcard p⟩

end PMHadrons.Occupancy
