import PMElementaryParticles.RecordCoordinates
import PMSubstrate.Channels

/-!
# The finite channel code as signed-axis vectors

`labelIndex c = 2*axis + sign`.  For the **vector** glue class of one `D₄`
sector the minimal vectors are `±2 e_axis` in the doubled coordinates of
`PMSubstrate.Channels.boxVec`.  This file defines that explicit coordinate map
on the active-false part of `Channels` and proves its norm and glue class.

The active-true half is not assigned to a second class here: the vector-class
coordinate formula has no signed-axis form on either spinor class.  That
second-class map is the missing object named in the docs.
-/

noncomputable section
namespace PMElementaryParticles.ChannelVectors

open PMSubstrate.Channels
open PMElementaryParticles.RecordCoordinates
open PMElementaryParticles.ControlledGluedRegister
open PMElementaryParticles.ProtocolInventory

/-- The axis as a `Fin 4`. -/
def axisIndex (c : PMConstants.PacketGaugeActions.Channels) : Fin 4 :=
  ⟨axis c, by unfold axis; have := (labelIndex c).isLt; omega⟩

/-- Doubled-coordinate vector `sign * 2 e_axis`. -/
def vectorCoord (c : PMConstants.PacketGaugeActions.Channels) : Fin 4 → ℤ :=
  fun i => if i = axisIndex c then (if signBit c then 2 else -2) else 0

theorem vectorCoord_norm4 (c : PMConstants.PacketGaugeActions.Channels) :
    norm4 (vectorCoord c) = 4 := by
  unfold vectorCoord norm4
  rw [Finset.sum_eq_single (axisIndex c)]
  · by_cases h : signBit c <;> simp [h]
  · intro b _ hb; simp [hb]
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem vectorCoord_glueClass (c : PMConstants.PacketGaugeActions.Channels)
    (hc : active c = false) :
    glueClass (vectorCoord c) = 1 := by
  revert c
  decide +kernel

/-- On the active-false labels the signed-axis coordinate is injective. -/
theorem vectorCoord_injective_on_activeFalse :
    ∀ (c d : PMConstants.PacketGaugeActions.Channels),
      active c = false → active d = false → vectorCoord c = vectorCoord d → c = d := by
  decide +kernel

theorem activeFalse_card :
    (Finset.univ.filter fun c : PMConstants.PacketGaugeActions.Channels =>
      active c = false).card = 8 := by
  decide +kernel

/-- The map agrees with `labelRecord`: axis zero is the lepton axis and the
sign bit is the second coordinate. -/
theorem vectorCoord_axis_sign (c : PMConstants.PacketGaugeActions.Channels) :
    (axisIndex c).val = axis c ∧
      (vectorCoord c (axisIndex c) = if signBit c then 2 else -2) := by
  constructor
  · rfl
  · simp [vectorCoord]

end PMElementaryParticles.ChannelVectors
