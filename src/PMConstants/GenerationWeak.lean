import PMAction.GenerationCurrent
import PMConstants.CarrierRepresentation

/-!
# Which generation change the charged current's own carrier can make

Step 4 of the generation sector, continued. `GenerationCurrent`: within the convention, the change
`g → g + 1` on wall `true` is a single-wall carrier of class `g − 1` plus a glue move, and on wall
`false` the change `g → g − 1` uses a carrier of class `g + 1`. Here the class indices are the actual
ones (`PMAction.CarrierEvents.classLabel`, `PMSubstrate.Channels.glueClass`): index `0` is the vector
class, the class of the weak carriers (`CarrierRepresentation.V = Carrier 0`,
`CarrierActions.weak`).

* `weak_carrier_is_vector`: `CarrierRepresentation.V` is `Carrier 0`.
* `weak_edge_true`, `weak_edge_false`: a vector-class carrier makes exactly one generation change on
  each wall: `1 → 2` on wall `true`, `2 → 1` on wall `false`. Both join generations `1` and `2`.
* `heavy_edges_spinor`: every change into or out of generation `0` (the label-`v` generation, the
  heavy one of `GenerationMass`) uses a spinor-class carrier (index `1` or `2`), on either wall.

So the charged current's own carrier (vector class) makes only the change between the two light
generations, the Cabibbo transition. The changes involving the heavy generation need a spinor
carrier, which the weak events do not supply; spinor displacements touch the reference axis
(`PMFlavor.ExchangeAxis.spinor_touch`), so those carriers come through the reference node. That is
why `|V_ub|` and `|V_cb|` are node-suppressed and `|V_us|` is not: a structural reason, not an
assignment.

* `relative_orientation`: in the other balanced convention (types `(e (g − 1), e (g + 1))`), the same
  wall-`true` composite goes `g → g − 1`. So the cycle's direction is the relative orientation of the
  convention and the charged current's wall; exchanging both leaves it unchanged. Which
  `GenerationWalls` wall is "the reference's" is therefore a convention, and only this relative
  orientation is physical (it sets the sign of any CP phase, `PMFlavor.LinkFlux`).
-/

namespace PMConstants.GenerationWeak
open PMAction.GenerationSector PMAction.GenerationOrientation

theorem weak_carrier_is_vector : CarrierRepresentation.V = PMAction.CarrierEvents.Carrier 0 := rfl

/-- **On wall `true` the vector-class carrier makes exactly the change `1 → 2`.** -/
theorem weak_edge_true : ∀ g : Fin 3, g - 1 = 0 ↔ g = 1 := by decide

/-- **On wall `false` it makes exactly `2 → 1`.** -/
theorem weak_edge_false : ∀ g : Fin 3, (g + 1 = 0 ↔ g = 2) ∧ (g = 2 → g - 1 = 1) := by decide

/-- **Every change at generation `0` uses a spinor carrier**, on either wall: the outgoing change
`0 → 1` and the incoming `2 → 0` on wall `true` use classes `2` and `1`; on wall `false`, `0 → 2`
and `1 → 0` use classes `1` and `2`. -/
theorem heavy_edges_spinor :
    ((0 : Fin 3) - 1 ≠ 0 ∧ (2 : Fin 3) - 1 ≠ 0) ∧ ((0 : Fin 3) + 1 ≠ 0 ∧ (1 : Fin 3) + 1 ≠ 0) := by
  decide

/-- **In the other convention the wall-`true` composite runs backwards.** Type
`(e (g − 1), e (g + 1))`: shift wall `true` by `e (g + 1)`, glue by the new label `e (g − 1)`, land on
the type of `g − 1`. -/
theorem relative_orientation : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    (e (g - 1) + e (g + 1) + e (g - 1), e (g + 1) + e (g - 1)) = (e (g - 1 - 1), e (g - 1 + 1)) := by
  decide +kernel

end PMConstants.GenerationWeak
