import PMHadrons.Occupancy
import PMSubstrate.TollFilters
import Mathlib.Tactic

/-!

# The strange carrier's extra occupancy is the Protocol direction count

The meson ledger is `mass = n · α⁻¹ + residual`, with `n = χ` (pion) and `n = σ + χ` (kaon)
(`MesonMasses`). `Occupancy` derived the colour-singlet base `nπ ≥ χ` from colour neutrality.
This module isolates the kaon's extra `σ` and identifies it.

**`σ` is the Protocol pillar's address count.** `σ = 5` is the vertex's interaction-direction
count (three spatial positions plus two boundary points). The defect's embedding occupies `σ` of
the `R_M = 172` cycle addresses; Protocol — the pillar that coordinates the successor state,
i.e. the one that *keeps the system going* — routes among the `R_M − σ = 167` residual addresses
(`PMSubstrate.TollFilters.residual_card`, `PMSubstrate.PersistenceEvents.protocol_persistence`).
So `σ` is a structural occupancy/direction count, not a fitted integer.

**Named hypothesis.** A **line-tier** carrier embeds the `σ` interaction directions, holding `σ`
addresses; a point-tier carrier holds one. The strange quark is down-type tier 1
(`PMElementaryParticles.TierLedger.downTiers`), so it is the mesons' line carrier. Then a meson
with `ℓ` line carriers holds `χ + σ·ℓ` cells:

* pion (`u d̄`, both point): `χ = 2`
* kaon (`u s̄`, one line): `χ + σ = 7`

This is still a named hypothesis — the `σ` is the interaction-direction count the Protocol pillar
already uses, so the remaining input is only "a line carrier spans the `σ` directions".
-/

namespace PMHadrons.StrangeCarrier

open Finset
open PMSubstrate.E8Values

/-- Interaction-direction count `σ` = three spatial + two boundary points. -/
abbrev directions : ℕ := sigma

/-- Colour-singlet base `χ` (the Map pillar count). -/
abbrev singletBase : ℕ := chi

/-- A line carrier embeds the `σ` interaction directions into the address cycle; the addresses it
holds are the image. -/
def lineFootprint {R : ℕ} (e : Fin directions → Fin R) : ℕ := (univ.image e).card

/-- **A line carrier holds `σ` addresses.** An injective placement of the interaction directions
occupies exactly `σ` of them. -/
theorem lineFootprint_eq {R : ℕ} (e : Fin directions → Fin R) (he : Function.Injective e) :
    lineFootprint e = directions := by
  unfold lineFootprint
  rw [card_image_of_injective _ he, card_univ, Fintype.card_fin]

/-- **Line footprint = Protocol's `σ`, with `R_M − σ` left residual.** The `σ` addresses a line
carrier holds are exactly the ones `residual_card` removes from the `R_M` cycle, leaving
`R_M − σ = 167` for Protocol to coordinate. -/
theorem lineFootprint_compl {R : ℕ} (e : Fin directions → Fin R) (he : Function.Injective e) :
    (univ \ univ.image e).card = R - directions :=
  PMSubstrate.TollFilters.residual_card e he

/-- Meson occupancy: the colour-singlet base plus the line carriers' direction footprints. -/
def mesonOccupancy (line : ℕ) : ℕ := singletBase + directions * line

theorem pion_occupancy : mesonOccupancy 0 = 2 := by decide

theorem kaon_occupancy : mesonOccupancy 1 = 7 := by decide

/-- **Occupied + residual = the cycle.** The `σ` addresses a line carrier holds plus Protocol's
residual fill the `R_M` cycle. -/
theorem occupied_add_residual : directions + (RM - directions) = RM := by decide

/-- The residual address count Protocol coordinates among. -/
theorem residual_eq : RM - directions = 167 := by decide

/-- The pion mass is the occupancy form at `n = χ`. -/
theorem pion_mass_eq :
    PMHadrons.MesonMasses.pionPlus =
      PMHadrons.Occupancy.occupancyMass (mesonOccupancy 0)
        PMHadrons.MesonMasses.pionPlusResidual := by
  rw [pion_occupancy]
  exact PMHadrons.Occupancy.pionPlus_eq_occupancyMass

/-- The kaon mass is the occupancy form at `n = χ + σ`. -/
theorem kaon_mass_eq :
    PMHadrons.CompositeMasses.kaonPlus =
      PMHadrons.Occupancy.occupancyMass (mesonOccupancy 1)
        PMHadrons.MesonMasses.kaonPlusResidual := by
  rw [kaon_occupancy]
  exact PMHadrons.Occupancy.kaonPlus_eq_occupancyMass

/-- The neutral pion mass is the occupancy form at `n = χ`. -/
theorem pion0_mass_eq :
    PMHadrons.CompositeMasses.pion0 =
      PMHadrons.Occupancy.occupancyMass (mesonOccupancy 0)
        PMHadrons.MesonMasses.pion0Residual := by
  rw [pion_occupancy]
  exact PMHadrons.Occupancy.pion0_eq_occupancyMass

/-- The neutral kaon mass is the occupancy form at `n = χ + σ`. -/
theorem kaon0_mass_eq :
    PMHadrons.CompositeMasses.kaon0 =
      PMHadrons.Occupancy.occupancyMass (mesonOccupancy 1)
        PMHadrons.MesonMasses.kaon0Residual := by
  rw [kaon_occupancy]
  exact PMHadrons.Occupancy.kaon0_eq_occupancyMass

/-- **Every meson ledger is the occupancy form `χ + σ·ℓ`.** The charged and neutral pion have no
line carrier (`ℓ = 0`), the charged and neutral kaon one (`ℓ = 1`). -/
theorem meson_ledgers :
    (PMHadrons.MesonMasses.pionPlus =
        PMHadrons.Occupancy.occupancyMass (mesonOccupancy 0) PMHadrons.MesonMasses.pionPlusResidual) ∧
      (PMHadrons.CompositeMasses.pion0 =
        PMHadrons.Occupancy.occupancyMass (mesonOccupancy 0) PMHadrons.MesonMasses.pion0Residual) ∧
      (PMHadrons.CompositeMasses.kaonPlus =
        PMHadrons.Occupancy.occupancyMass (mesonOccupancy 1) PMHadrons.MesonMasses.kaonPlusResidual) ∧
      (PMHadrons.CompositeMasses.kaon0 =
        PMHadrons.Occupancy.occupancyMass (mesonOccupancy 1) PMHadrons.MesonMasses.kaon0Residual) :=
  ⟨pion_mass_eq, pion0_mass_eq, kaon_mass_eq, kaon0_mass_eq⟩

/-! ## The carrier direction register (the line-carrier premise)

A vertex's interaction direction is one of `σ` (three spatial positions plus two boundary points;
`PMSubstrate.PersistencePremises.flipOrientation` acts on `Fin 5`). The modelling content of the
line-carrier premise is that a directional carrier holds its **whole** direction register — just
as a boundary holds its full orientation space (`PMSubstrate.Arity.Orientation.two_orientations`).
With that, `n = χ + σ·ℓ` is a theorem, not an input. -/

/-- The vertex interaction-direction space. -/
abbrev Direction : Type := Fin directions

/-- **The carrier direction register.** A point-tier carrier resolves no direction beyond its
reference and holds one; a line-tier carrier resolves its direction among the `σ` directions and
holds the whole register. -/
def directionRegister (line : Bool) : Finset Direction :=
  if line then univ else {⟨0, by decide⟩}

theorem directionRegister_card (line : Bool) :
    (directionRegister line).card = if line then directions else 1 := by
  cases line <;> decide

/-- **A line carrier holds all `σ` interaction directions.** -/
theorem line_register_card : (directionRegister true).card = directions := by
  rw [directionRegister_card]; simp

/-- The meson occupancy is the singlet base plus `line` line-carrier direction registers. -/
theorem mesonOccupancy_eq_register (line : ℕ) :
    mesonOccupancy line = singletBase + (directionRegister true).card * line := by
  rw [line_register_card]
  rfl

end PMHadrons.StrangeCarrier
