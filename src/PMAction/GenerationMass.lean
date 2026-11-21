import PMAction.GenerationOrientation

/-!
# A generation-diagonal mass from allowed moves: a crossing and a label-class carrier

Step 3 of the generation sector (`PMAction/TODO.md`). Within one orientation convention
(`GenerationWalls.side`: generation `g` carries class `g + 1` on wall `true`, `g − 1` on wall
`false`), wall is chirality (`PMAction.DomainWall`), so a mass joins a generation's two walls.

**No single allowed move does it.**
* `diagonal_flip_changes_class`: a generation's two wall classes differ, so a generation-diagonal
  chirality flip changes the class, by the label (`GenerationOrientation.type_label`). The gluing
  joins only equal classes, so this is not one move.
* `crossing_changes_generation`: the equal-class crossing, the move the gluing does allow, lands in
  another generation (as `PMAction.InterWallDiagonal`).

**Two allowed moves do.** An equal-class crossing and a single-wall carrier, in either order:
* `composite_cross_then_shift`: cross generation `g`'s wall-`true` class `g + 1` to wall `false`
  (landing in generation `g + 2`), then shift wall `false` from class `g + 1` to `g − 1`; the result
  is generation `g` on wall `false`.
* `composite_shift_then_cross`: shift wall `true` from `g + 1` to `g − 1` (landing in generation
  `g + 1`), then cross class `g − 1`; again generation `g` on wall `false`.
* `composite_carrier_is_label`: in both orders the carrier's class change is
  `e (g + 1) + e (g − 1) = e g`, the generation's own label, the insertion `PMAction.MassInsertion`
  requires (`bilinear_gap`). The intermediate is another generation, so the composite is second
  order.

**Amplitudes (reading, with its sources).** The crossing is the inter-sector hop of
`PMAction.DomainWall`, the same for every class, so it gives a common factor `y`. The carrier is a
single-wall displacement, so `PMFlavor.ExchangeAxis` applies: six of eight vector-class
displacements avoid the reference axis (in-cycle), every spinor-class displacement touches it (a
node crossing). So `m_g ∝ y · κ_{label g}`, with `κ` unsuppressed for the label-`v` generation and
node-suppressed for the two others: one heavy generation and two light ones, the heavy one being the
generation whose two mixings both cross the node (`PMAction.GenerationSector`,
`PMAction.MassInsertion`). That is the observed pattern (one heavy, weakly mixed generation). Not
fixed here: the size of the node factor (the leg rule gives `α⁻¹` or `α^{−1/2}` and does not match
the measured heavy/middle ratios, `PMFlavor/TODO.md`), and the split of the two light
generations, which are degenerate at this order (their insertions are the two spinor classes; the
weak wall distinguishes them, `PMFlavor.ExchangeChirality`).
-/

namespace PMAction.GenerationMass
open PMAction.GenerationSector GenerationOrientation GenerationWalls

/-- **A generation's two wall classes differ.** -/
theorem diagonal_flip_changes_class : ∀ g : Fin 3, g + 1 ≠ g - 1 := by decide

/-- **The equal-class crossing lands in another generation.** -/
theorem crossing_changes_generation : ∀ (b : Bool) (c : Fin 3), omitted b c ≠ omitted (!b) c := by
  decide

/-- **Cross, then shift**: the crossing of class `g + 1` lands in generation `g + 2`; class `g − 1`
on wall `false` is generation `g`. -/
theorem composite_cross_then_shift : ∀ g : Fin 3,
    omitted false (g + 1) = g + 2 ∧ g + 2 ≠ g ∧ omitted false (g - 1) = g := by decide

/-- **Shift, then cross**: class `g − 1` on wall `true` is generation `g + 1`; the crossing of class
`g − 1` lands in generation `g`. -/
theorem composite_shift_then_cross : ∀ g : Fin 3,
    omitted true (g - 1) = g + 1 ∧ g + 1 ≠ g ∧ omitted false (g - 1) = g := by decide

/-- **The carrier's class is the generation's own label**, in either order. -/
theorem composite_carrier_is_label : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    e (g + 1) + e (g - 1) = e g := by
  decide +kernel

end PMAction.GenerationMass
