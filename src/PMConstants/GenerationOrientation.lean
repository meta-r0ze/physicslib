import PMConstants.GenerationWalls
import PMAction.GenerationSector

/-!
# The two generation encodings are one, up to a frozen orientation

`PMAction.GenerationSector` describes a generation by its glue classes on the two walls, an ordered
pair `(b, c)` with label `b + c` (as `PMFlavor.GenerationLabel`). `GenerationWalls` indexes a
generation `g` by the classes it carries, `g + 1` on wall `true` and `g − 1` on wall `false`
(`side`). This module relates them, for **every** identification `e` of `Fin 3` with the three
nontrivial classes (`Good e`), so no identification is chosen.

* `type_is_gen`, `type_label`: `GenerationWalls`' generation `g` is the pair
  `(e (g + 1), e (g − 1))`, a generation state whose label is `e g`. The two indices agree.
* `side_classes`: those are the classes `side` assigns to the two walls.
* `orientation_split`: the three `GenerationWalls` types and their reversals are disjoint, so
  `side` picks exactly one of the two orientations of every label.
* `swap_keeps_label`: swapping the walls of a whole generation, `(b, c) ↦ (c, b)`, keeps the label
  (it is the label translation of `GenerationSector.label_glue_swaps`). `swap_leaves_convention`:
  the swapped type is not one of `GenerationWalls`' types; read in that convention its two walls'
  classes belong to two different generations (`g + 1` and `g − 1`). So `GenerationWalls`' index is
  the label with the orientation frozen, and the statement that a wall crossing changes the
  generation (`exchange_not_generation_only`) is, in label terms, that it reverses the orientation.
* `single_crossing_unequal`: moving one component across the walls at a fixed class
  (`GenerationWalls.exchange`) takes type `g − 1` to type `g + 1`, which changes the two walls'
  classes by **different** nontrivial amounts (`e (g + 1)` on one wall, `e (g − 1)` on the other). That
  is neither an `E₈` translation (equal amounts) nor a single-wall shift (one wall), so it is not one
  of the moves `GenerationSector` allows. Whether it is a physical move is open (chirality, step 3 in
  `PMAction/REVIEW-AND-NEXT.md`).
-/

namespace PMConstants.GenerationOrientation
open PMAction.GenerationSector

/-- An identification of `Fin 3` with the three nontrivial glue classes. -/
def Good (e : Fin 3 → Glue) : Prop :=
  e 0 ≠ 0 ∧ e 1 ≠ 0 ∧ e 2 ≠ 0 ∧ e 0 ≠ e 1 ∧ e 0 ≠ e 2 ∧ e 1 ≠ e 2

instance (e : Fin 3 → Glue) : Decidable (Good e) := by unfold Good; infer_instance

/-- The classes `side` puts on the two walls of generation `g`. -/
theorem side_classes : ∀ g : Fin 3,
    GenerationWalls.side g (g + 1) = true ∧ GenerationWalls.side g (g - 1) = false := by decide

/-- **`GenerationWalls`' generation `g` is a generation state.** -/
theorem type_is_gen : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3, IsGen (e (g + 1)) (e (g - 1)) := by
  decide +kernel

/-- **Its label is `e g`**: the two indices agree. -/
theorem type_label : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3, e (g + 1) + e (g - 1) = e g := by
  decide +kernel

/-- **`side` picks one orientation per label**: no type is the reversal of another. -/
theorem orientation_split : ∀ e : Fin 3 → Glue, Good e → ∀ g h : Fin 3,
    (e (h + 1), e (h - 1)) ≠ (e (g - 1), e (g + 1)) := by decide +kernel

/-- **Swapping the walls of a whole generation keeps its label.** -/
theorem swap_keeps_label : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    e (g - 1) + e (g + 1) = e g := by decide +kernel

/-- **The swapped type leaves the convention**: its wall-`true` class `e (g − 1)` belongs to
`GenerationWalls`' generation `g + 1` (`= (g − 1) − 1`), its wall-`false` class `e (g + 1)` to
generation `g − 1`. -/
theorem swap_leaves_convention : ∀ g : Fin 3,
    GenerationWalls.omitted true (g - 1) = g + 1 ∧ GenerationWalls.omitted false (g + 1) = g - 1 := by
  decide

/-- **A single component crossing changes the two walls by different amounts.** Type `g − 1`
(classes `e g`, `e (g + 1)`) goes to type `g + 1` (classes `e (g − 1)`, `e g`): wall `true` changes by
`e g + e (g − 1) = e (g + 1)`, wall `false` by `e (g + 1) + e g = e (g − 1)`, both nontrivial and
unequal. -/
theorem single_crossing_unequal : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    e g + e (g - 1) ≠ 0 ∧ e (g + 1) + e g ≠ 0 ∧ e g + e (g - 1) ≠ e (g + 1) + e g := by decide +kernel

end PMConstants.GenerationOrientation
