import PMElementaryParticles.ControlledGluedRegister
import PMElementaryParticles.HeavyFlipControl
import PMSubstrate.Channels

/-!
# Record bits as signed-axis coordinates

`ControlledGluedRegister.labelIndex` has eight values.  For colour labels it is
`2*(axis+1) + sign`, for lepton labels `sign`; equivalently
`index = 2*axis + sign` with axis `0` the lepton axis and axes `1,2,3` the
colour axes.  `HeavyFlipControl.labelRecord` is `(axis = 0, sign = 1)`.

This is a verified coordinate statement about the finite packet code.  It does
**not** by itself identify the eight `labelIndex` values with the eight minimal
vectors of a `D₄` glue class: `PMSubstrate.Channels` proves each nontrivial
class has eight minimal vectors, but no theorem supplies the bijection between
`Fin 8` here and those vectors.  The missing map is named in the docs.
-/

noncomputable section
namespace PMElementaryParticles.RecordCoordinates

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ControlledGluedRegister
open PMElementaryParticles.HeavyFlipControl

/-- Axis coordinate of the signed label. -/
def axis (c : Channels) : ℕ := (labelIndex c).val / 2

/-- Sign coordinate of the signed label. -/
def signBit (c : Channels) : Bool := (labelIndex c).val % 2 = 1

theorem labelIndex_decomp (c : Channels) :
    (labelIndex c).val = 2 * axis c + (labelIndex c).val % 2 := by
  unfold axis
  omega

/-- `labelRecord` is exactly `(axis = 0, sign = 1)`. -/
theorem labelRecord_eq_axis_sign (c : Channels) :
    labelRecord c = (decide (axis c = 0), signBit c) := by
  unfold labelRecord axis signBit
  congr 1
  exact decide_eq_decide.mpr (by omega : (labelIndex c).val < 2 ↔ (labelIndex c).val / 2 = 0)

/-- The alternative lead form `(index < 2, index odd)` is definitionally the
same coordinate pair. -/
theorem labelRecord_coordinates (c : Channels) :
    labelRecord c = (decide ((labelIndex c).val < 2),
      decide ((labelIndex c).val % 2 = 1)) := rfl

/-- The finite code has eight signed axes and two walls. -/
theorem channelCode_card :
    Fintype.card (Bool × Fin 8) = 16 := by decide +kernel

end PMElementaryParticles.RecordCoordinates
