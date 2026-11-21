import PMAction.GenerationMass

/-!
# Generation changes within one convention: a carrier and a glue move, a directed cycle per wall

Step 4 of the generation sector (`PMAction/TODO.md`). In the orientation convention of
`GenerationWalls` (generation `g` is the pair `(e (g + 1), e (g − 1))` on walls `true`/`false`,
`GenerationOrientation`), which moves change the generation?

* `no_single_shift_changes`: no single-wall shift does. A shift that keeps a generation state
  (`PMAction.GenerationSector.shift_keeps_iff`) reverses its orientation, so it leaves the
  convention; within the convention a single-wall shift reaches no other generation.
* `shift_true_then_glue`: a shift on wall `true` by the other wall's class `e (g − 1)`, followed by
  the `E₈` glue translation by `e (g + 1)` (the intermediate's label), lands on generation `g + 1`.
* `shift_false_then_glue`: the same on wall `false` (carrier `e (g + 1)`, glue `e (g − 1)`) lands on
  generation `g − 1`.

So every generation change within the convention is one single-wall carrier plus one `E₈` glue
move, and on a given wall the changes form a directed 3-cycle: `g → g + 1` on wall `true`,
`g → g − 1` on wall `false`. The charged current acts on one wall (`PMAction.WallChiralCurrent`), so
its generation changes go one way around the cycle; which wall it is sets the orientation, the
same orientation that sets the sign of any CP phase (`PMFlavor.LinkFlux`).

`edge_carrier`: on wall `true` the change `g → g + 1` uses a carrier of class `e (g − 1)`. So the
one edge whose carrier is the reference's class `v` joins the two generations other than the label-`v`
one, and both edges at the label-`v` generation use spinor carriers. With `PMFlavor.ExchangeAxis`
(vector displacements mostly in-cycle, spinor ones through the node), the edge between the two light
generations is unsuppressed and both edges at the heavy generation are node-suppressed: the coarse
CKM pattern (`|V_us|` large, `|V_ub|`, `|V_cb|` small). The mass composite (`GenerationMass`) and the
generation change share the single-wall carrier, so masses and mixings share its amplitudes.
-/

namespace PMAction.GenerationCurrent
open PMAction.GenerationSector GenerationOrientation

/-- **No single-wall shift reaches another generation within the convention.** -/
theorem no_single_shift_changes : ∀ e : Fin 3 → Glue, Good e → ∀ g h : Fin 3, ∀ a : Glue,
    ((e (g + 1) + a, e (g - 1)) = (e (h + 1), e (h - 1)) → h = g) ∧
    ((e (g + 1), e (g - 1) + a) = (e (h + 1), e (h - 1)) → h = g) := by
  decide +kernel

/-- **Wall `true`: shift by the other wall's class, then the glue move by the new label**, lands
on generation `g + 1`. -/
theorem shift_true_then_glue : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    (e (g + 1) + e (g - 1) + e (g + 1), e (g - 1) + e (g + 1)) = (e (g + 1 + 1), e (g + 1 - 1)) := by
  decide +kernel

/-- **Wall `false`**: shift by `e (g + 1)`, glue by `e (g − 1)`, lands on generation `g − 1`. -/
theorem shift_false_then_glue : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    (e (g + 1) + e (g - 1), e (g - 1) + e (g + 1) + e (g - 1)) = (e (g - 1 + 1), e (g - 1 - 1)) := by
  decide +kernel

/-- **The glue move's class is the intermediate's label** `e (g + 1)` (wall `true`). -/
theorem glue_is_intermediate_label : ∀ e : Fin 3 → Glue, Good e → ∀ g : Fin 3,
    (e (g + 1) + e (g - 1)) + e (g - 1) = e (g + 1) := by
  decide +kernel

/-- **The edge carrier.** On wall `true` the change `g → g + 1` uses a carrier of class
`e (g − 1)`; it is the class `e v` exactly when `g = v + 1`, the edge between `v + 1` and `v + 2`,
which does not touch generation `v`. -/
theorem edge_carrier : ∀ e : Fin 3 → Glue, Good e → ∀ g v : Fin 3,
    (e (g - 1) = e v ↔ g = v + 1) ∧ (g = v + 1 → g ≠ v ∧ g + 1 ≠ v) := by
  decide +kernel

end PMAction.GenerationCurrent
