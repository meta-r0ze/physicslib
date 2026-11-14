import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The generation sector of the update: which moves keep or change a generation

Foundation for the flavour sector (`PMFlavor`), which reached several forks it could not settle
without knowing what the update itself does to generations. This module inventories the moves on the
glue-class labels, exhaustively.

**State.** `E₈` is the gluing of `D₄ ⊕ D₄` by equal glue classes (`PMSubstrate.ChannelSymmetry`).
A generation state puts a nontrivial class `b` on wall 1 and a nontrivial class `c ≠ b` on wall 2
(`IsGen`), an off-diagonal coset of `D₄* ⊕ D₄*`; its label is `b + c`, the third class
(`PMFlavor.GenerationLabel`). There are six ordered pairs (`gen_count`), two orientations per label.
`PMConstants.GenerationWalls` instead encodes a generation's modes as single carriers on one wall;
relating the two state spaces is the next step (`REVIEW-AND-NEXT.md`).

**E₈ moves (translations by `(a, a)`).**
* `glue_conserves_label`: they conserve the label.
* `glue_keeps_iff`: on a generation state they give a generation state exactly for `a = 0` (a `D₄`
  root move, classes unchanged) or `a = b + c`, the label.
* `label_glue_swaps`: translation by the label swaps the two classes between the walls,
  `(b, c) ↦ (c, b)`. It keeps the label and reverses the orientation. Caution: the vacuum fixes
  one orientation per label (`PMConstants.GenerationWalls.side`, one of two balanced conventions),
  and the 48 modes leave no room for the other (`no_further_modes`), so this translation maps
  between the two conventions; it is not an operator within the physical mode space of one
  convention (`PMConstants.GenerationOrientation`). Within one convention a generation-diagonal
  chirality flip changes the class by the label, which the gluing (equal classes) does not allow
  as a single move.

**Single-wall moves (a `D₄*` carrier on one wall, not an `E₈` vector).**
* `shift_keeps_iff`: shifting wall 1 by a nontrivial class `a` keeps a generation state exactly when
  `a = c`, the class on the other wall; `shift_new_label`: the label then becomes `b`. Likewise on
  wall 2 (`shift2_keeps_iff`, label becomes `c`).
* So every generation change is a non-`E₈` single-carrier move, and from generation `(b, c)` the
  change to label `b` is a class-`c` carrier on wall 1 and the change to label `c` a class-`b`
  carrier on wall 2: one wall for each target.

What this fixes for flavour: within one convention no `E₈` move is a generation-diagonal mass, and
mixing cannot be an `E₈` move either; it needs single-carrier events, each tied to one wall. Which wall the
charged current acts on (the reference's) then decides which generation changes the charged current
can make; that, the orientation, and the relation to the wall-encoded modes are the next items.
-/

namespace PMAction.GenerationSector

/-- The glue group `D₄*/D₄`. -/
abbrev Glue := ZMod 2 × ZMod 2

/-- A generation state: distinct nontrivial classes on the two walls. -/
def IsGen (b c : Glue) : Prop := b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c

instance (b c : Glue) : Decidable (IsGen b c) := by unfold IsGen; infer_instance

/-- **Six ordered pairs**, two orientations for each of the three labels. -/
theorem gen_count :
    (Finset.univ.filter (fun p : Glue × Glue => IsGen p.1 p.2)).card = 6 := by decide

/-- `E₈` translations conserve the label. -/
theorem glue_conserves_label (b c a : Glue) : (b + a) + (c + a) = b + c := by
  have h : a + a = 0 := by revert a; decide
  calc (b + a) + (c + a) = (b + c) + (a + a) := by abel
    _ = b + c := by rw [h, add_zero]

/-- **An `E₈` translation keeps a generation state exactly for `a = 0` or `a = label`.** -/
theorem glue_keeps_iff : ∀ b c a : Glue, IsGen b c →
    (IsGen (b + a) (c + a) ↔ a = 0 ∨ a = b + c) := by decide

/-- **Translation by the label swaps the classes between the walls.** -/
theorem label_glue_swaps : ∀ b c : Glue, IsGen b c →
    b + (b + c) = c ∧ c + (b + c) = b := by decide

/-- **A wall-1 shift keeps a generation state exactly when it is the other wall's class.** -/
theorem shift_keeps_iff : ∀ b c a : Glue, IsGen b c → a ≠ 0 →
    (IsGen (b + a) c ↔ a = c) := by decide

/-- After the wall-1 shift by `c`, the label is `b`. -/
theorem shift_new_label : ∀ b c : Glue, IsGen b c → (b + c) + c = b := by decide

/-- **The same on wall 2**: a shift by `a` keeps a generation state exactly when `a = b`, and the
label becomes `c`. -/
theorem shift2_keeps_iff : ∀ b c a : Glue, IsGen b c → a ≠ 0 →
    (IsGen b (c + a) ↔ a = b) ∧ (a = b → b + (c + a) = c) := by decide

end PMAction.GenerationSector
