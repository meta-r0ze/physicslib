import PMAction.GenerationLabel
import PMAction.GenerationSector

/-!
# A sign flip on one wall keeps the label

A wall state sits in a glue class of `D₄*/D₄ = ZMod 2 × ZMod 2` (`GenerationSector`). Reversing the
sign of a carrier, `x ↦ −x`, moves it by `−2x`, and `2x` lies in `D₄`: the move is in the trivial
class. A label change, in contrast, is a single-wall shift by a nontrivial class
(`GenerationSector.shift_keeps_iff`, `GenerationCurrent`).

* `neg_class`: negation is the identity on glue classes (exponent `2`).
* `flip_move_trivial`: the flip's displacement `−b − b` is the trivial class.
* `flip_keeps_state`: on a generation state the flip keeps the state and its label.
* `flip_not_label_change`: no nontrivial shift `a` reproduces the flip's class, so a sign flip is
  never one of the label changes.

Used by `PMFlavor.RefreshLabel`: the weak refresh is a sign flip of the reference's sector
(`PMConstants.CarrierActions.weak`), so it changes the doublet position and keeps the label.
-/

namespace PMAction.SignFlip
open PMAction.GenerationSector

/-- **Negation is the identity on glue classes.** -/
theorem neg_class : ∀ g : Glue, -g = g := by decide

/-- **The flip's displacement is in the trivial class.** -/
theorem flip_move_trivial : ∀ g : Glue, -g - g = 0 := by decide

/-- **A sign flip on wall 1 keeps the generation state and its label.** -/
theorem flip_keeps_state : ∀ b c : Glue, IsGen b c →
    IsGen (-b) c ∧ GenerationLabel.label (-b) c = GenerationLabel.label b c := by decide

/-- **A sign flip is not a label change**: no nontrivial shift lands on the flipped class. -/
theorem flip_not_label_change : ∀ b a : Glue, a ≠ 0 → b + a ≠ -b := by decide

end PMAction.SignFlip
