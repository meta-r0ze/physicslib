import PMElementaryParticles.EPSpine
import PMElementaryParticles.ProtocolInventory

/-!
# The derived gauge sector and one channel placement (certificate)

This module checks, by `decide`, the gauge sector and channel placement that the
persistence readings select (`tools/pm_sector/`; `OVERVIEW.md`, section "Gauge sector and
mass pairs"). It certifies one representative placement. It does not prove that the sector or
the placement is forced; those eliminations are separate.

* The sector is the internal D4 and two orthogonal clock-silent spacetime roots: `weak` (the
  weak flip) and `chargeRoot`. Colour reflects in `colourA`, `colourB` (internal D4).
* `timeVec` is the clock time vector: the sum of two orthogonal forward clock-axis roots. Every
  forward clock-axis root pairs `2` with it. The gauge roots are orthogonal to it.
* `chargeDir` is an E8 vector orthogonal to the colour, weak and time directions. Its pairing
  with a placed channel is `3Y` (`charge3`), the diagonal of `PacketGaugeActions.charge`.
* `placement g` puts the 16 channels of generation `g` (`EPSector.sectorIndex` order) on E8
  roots. Reflection in `weak` is `flipWeak`; reflection in `colourA`, `colourB` is
  `permuteColour 0 1`, `permuteColour 1 2`.
* Walls: in each generation all doublets have one glue key and all singlets another, and
  neither is the generation's own key (`placement_walls`).
* Mass pairs: in generations 1 and 2 the up flip `u − Q_up` is a root (norm 2) and the down
  flip `d − Q_down` has norm 4 (`up_flip_one_step`, `down_flip_two_steps`).
-/

namespace PMElementaryParticles.GaugeSector

open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment
open PMConstants.PacketGaugeActions

/-- Reflection of `z` in the root `a`. -/
def refl (a z : V) : V := fun i => z i - pair z a * a i

/-- Colour reflection root realizing `permuteColour 0 1`. -/
def colourA : V := ![0, -1, -1, -2, -1, 0, 0, 0]
/-- Colour reflection root realizing `permuteColour 1 2`. -/
def colourB : V := ![0, -1, -1, -1, -1, 0, 0, 0]
/-- Weak-flip root (clock-silent spacetime root). -/
def weak : V := ![-2, -3, -4, -6, -5, -4, -3, -1]
/-- Second clock-silent spacetime root of the sector; it carries the charge direction. -/
def chargeRoot : V := ![0, 0, 0, 0, 0, 0, -1, -1]
/-- Clock time vector. -/
def timeVec : V := ![2, 1, 2, 2, 1, 0, 0, 0]
/-- Charge direction: pairing with a placed channel is `3Y`. -/
def chargeDir : V := ![0, 1, -2, 0, 1, 0, 3, 3]

/-- `3Y` from the diagonal of `PacketGaugeActions.charge`. -/
def charge3 : Channels → ℤ
  | .inl _ => 1
  | .inr (.inl (_, 0)) => 4
  | .inr (.inl (_, 1)) => -2
  | .inr (.inr (.inl _)) => -3
  | .inr (.inr (.inr 0)) => 0
  | .inr (.inr (.inr 1)) => -6

/-- Generation `(0,1)` (index 0): one representative placement. -/
def placement0 : Channels → V
  | .inl (0, 0) => ![-1, -1, -2, -3, -2, -1, -1, 0]
  | .inl (0, 1) => ![1, 2, 2, 3, 3, 3, 2, 1]
  | .inl (1, 0) => ![-1, 0, -1, -1, -1, -1, -1, 0]
  | .inl (1, 1) => ![1, 3, 3, 5, 4, 3, 2, 1]
  | .inl (2, 0) => ![-1, -1, -2, -2, -2, -1, -1, 0]
  | .inl (2, 1) => ![1, 2, 2, 4, 3, 3, 2, 1]
  | .inr (.inl (0, 0)) => ![0, 0, 0, 0, 1, 1, 1, 1]
  | .inr (.inl (0, 1)) => ![0, 0, 0, 0, 1, 1, 0, 0]
  | .inr (.inl (1, 0)) => ![0, 1, 1, 2, 2, 1, 1, 1]
  | .inr (.inl (1, 1)) => ![0, 1, 1, 2, 2, 1, 0, 0]
  | .inr (.inl (2, 0)) => ![0, 0, 0, 1, 1, 1, 1, 1]
  | .inr (.inl (2, 1)) => ![0, 0, 0, 1, 1, 1, 0, 0]
  | .inr (.inr (.inl 0)) => ![-1, -1, -1, -2, -2, -1, -1, 0]
  | .inr (.inr (.inl 1)) => ![1, 2, 3, 4, 3, 3, 2, 1]
  | .inr (.inr (.inr 0)) => ![0, -1, 0, -1, -1, -1, 0, 0]
  | .inr (.inr (.inr 1)) => ![0, -1, 0, -1, -1, -1, -1, -1]

/-- Generation `(1,0)` (index 1): one representative placement. -/
def placement1 : Channels → V
  | .inl (0, 0) => ![-1, -2, -2, -4, -3, -2, -1, 0]
  | .inl (0, 1) => ![1, 1, 2, 2, 2, 2, 2, 1]
  | .inl (1, 0) => ![-1, -1, -1, -2, -2, -2, -1, 0]
  | .inl (1, 1) => ![1, 2, 3, 4, 3, 2, 2, 1]
  | .inl (2, 0) => ![-1, -2, -2, -3, -3, -2, -1, 0]
  | .inl (2, 1) => ![1, 1, 2, 3, 2, 2, 2, 1]
  | .inr (.inl (0, 0)) => ![0, 0, 0, 0, 1, 1, 1, 1]
  | .inr (.inl (0, 1)) => ![0, -1, -1, -2, -1, -1, -1, -1]
  | .inr (.inl (1, 0)) => ![0, 1, 1, 2, 2, 1, 1, 1]
  | .inr (.inl (1, 1)) => ![0, 0, 0, 0, 0, -1, -1, -1]
  | .inr (.inl (2, 0)) => ![0, 0, 0, 1, 1, 1, 1, 1]
  | .inr (.inl (2, 1)) => ![0, -1, -1, -1, -1, -1, -1, -1]
  | .inr (.inr (.inl 0)) => ![-1, -1, -2, -3, -3, -2, -2, -1]
  | .inr (.inr (.inl 1)) => ![1, 2, 2, 3, 2, 2, 1, 0]
  | .inr (.inr (.inr 0)) => ![0, -1, 0, -1, -1, -1, 0, 0]
  | .inr (.inr (.inr 1)) => ![0, -1, 0, -1, -1, -1, -1, -1]

/-- Generation `(1,1)` (index 2): one representative placement. -/
def placement2 : Channels → V
  | .inl (0, 0) => ![-1, -2, -2, -4, -3, -2, -1, 0]
  | .inl (0, 1) => ![1, 1, 2, 2, 2, 2, 2, 1]
  | .inl (1, 0) => ![-1, -1, -1, -2, -2, -2, -1, 0]
  | .inl (1, 1) => ![1, 2, 3, 4, 3, 2, 2, 1]
  | .inl (2, 0) => ![-1, -2, -2, -3, -3, -2, -1, 0]
  | .inl (2, 1) => ![1, 1, 2, 3, 2, 2, 2, 1]
  | .inr (.inl (0, 0)) => ![1, 1, 1, 1, 1, 1, 1, 1]
  | .inr (.inl (0, 1)) => ![1, 1, 1, 1, 1, 1, 0, 0]
  | .inr (.inl (1, 0)) => ![1, 2, 2, 3, 2, 1, 1, 1]
  | .inr (.inl (1, 1)) => ![1, 2, 2, 3, 2, 1, 0, 0]
  | .inr (.inl (2, 0)) => ![1, 1, 1, 2, 1, 1, 1, 1]
  | .inr (.inl (2, 1)) => ![1, 1, 1, 2, 1, 1, 0, 0]
  | .inr (.inr (.inl 0)) => ![-1, -2, -2, -3, -2, -2, -2, -1]
  | .inr (.inr (.inl 1)) => ![1, 1, 2, 3, 3, 2, 1, 0]
  | .inr (.inr (.inr 0)) => ![-1, -1, -2, -2, -1, -1, -1, -1]
  | .inr (.inr (.inr 1)) => ![-1, -1, -1, -2, -2, -1, -1, -1]

/-- The placement of generation `g`. -/
def placement : Fin 3 → Channels → V
  | 0 => placement0
  | 1 => placement1
  | 2 => placement2

theorem sector_roots_mem :
    colourA ∈ rootList ∧ colourB ∈ rootList ∧ weak ∈ rootList ∧ chargeRoot ∈ rootList := by
  decide +kernel

theorem placement_mem : ∀ g c, placement g c ∈ rootList := by decide +kernel

theorem sector_pairs :
    pair colourA colourB = 1 ∧ pair weak colourA = 0 ∧ pair weak colourB = 0 ∧
      pair chargeRoot colourA = 0 ∧ pair chargeRoot colourB = 0 ∧ pair weak chargeRoot = 0 := by
  decide

theorem sector_time :
    pair colourA timeVec = 0 ∧ pair colourB timeVec = 0 ∧ pair weak timeVec = 0 ∧
      pair chargeRoot timeVec = 0 := by
  decide

theorem sector_clock_silent : clockReading weak = 0 ∧ clockReading chargeRoot = 0 := by decide

theorem timeVec_forward_pair :
    ∃ f ∈ clockAxisRoots, ∃ f' ∈ clockAxisRoots, clockReading f = 1 ∧ clockReading f' = 1 ∧
      pair f f' = 0 ∧ timeVec = f + f' := by
  decide +kernel

theorem forward_pairs_two :
    ∀ f ∈ clockAxisRoots, clockReading f = 1 → pair f timeVec = 2 := by decide +kernel

theorem chargeDir_orthogonal :
    pair chargeDir colourA = 0 ∧ pair chargeDir colourB = 0 ∧ pair chargeDir weak = 0 ∧
      pair chargeDir timeVec = 0 := by
  decide

theorem placement_charge : ∀ g c, pair chargeDir (placement g c) = charge3 c := by decide

theorem weak_reflection : ∀ g c, refl weak (placement g c) = placement g (flipWeak c) := by decide

theorem colourA_reflection :
    ∀ g c, refl colourA (placement g c) = placement g (permuteColour 0 1 c) := by decide

theorem colourB_reflection :
    ∀ g c, refl colourB (placement g c) = placement g (permuteColour 1 2 c) := by decide

/-- Glue key of the doublets and of the singlets, per generation. -/
def wallKey : Fin 3 → Bool → ZMod 2 × ZMod 2
  | 0, true => (1, 0) | 0, false => (1, 1)
  | 1, true => (0, 1) | 1, false => (1, 1)
  | 2, true => (0, 1) | 2, false => (1, 0)

/-- Generation `g`'s own glue key (`EPSector.sectorIndex` order). -/
def ownKey : Fin 3 → ZMod 2 × ZMod 2
  | 0 => (0, 1) | 1 => (1, 0) | 2 => (1, 1)

theorem placement_walls :
    ∀ g c, glueKey (placement g c) = wallKey g (PMElementaryParticles.ProtocolInventory.active c) := by
  decide +kernel

theorem walls_not_own : ∀ g b, wallKey g b ≠ ownKey g ∧ wallKey g true ≠ wallKey g false := by
  decide

theorem up_flip_one_step : ∀ (g : Fin 3), g ≠ 0 → ∀ c : Fin 3,
    pair (placement g (.inr (.inl (c, 0))) - placement g (.inl (c, 0)))
      (placement g (.inr (.inl (c, 0))) - placement g (.inl (c, 0))) = 2 := by decide

theorem down_flip_two_steps : ∀ (g : Fin 3), g ≠ 0 → ∀ c : Fin 3,
    pair (placement g (.inr (.inl (c, 1))) - placement g (.inl (c, 1)))
      (placement g (.inr (.inl (c, 1))) - placement g (.inl (c, 1))) = 4 := by decide

end PMElementaryParticles.GaugeSector
