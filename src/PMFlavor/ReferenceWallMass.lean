import PMFlavor.LightSplit
import PMAction.ReferenceDetuning

/-!
# The light mass with no detuning on the reference's wall

`PMAction.ReferenceDetuning.stationary_iff`: the reference background, on the second wall, is a
stationary zero mode exactly when that wall's on-site detuning vanishes. The second wall is the
`D₂` slot of `CompositeMass` (wall `false`; `Y` maps it to wall `true`). So `δ_F = 0`, and the
light mass of `LightSplit.composite_expansion2` factors:

* `reference_wall_mass`: `M = cyc κ_R · Y⁻¹ · (δ_O + cyc κ_O) = D_R · (δ_O + cyc κ_O)`,
  `D_R = diag(κ_R/y)` (shifted to the generation index as in `CompositeMass.cyc_mul_cycInv`).

So the hierarchy is the reference-wall carriers `κ_R(e g)` of each generation's label class. The
right factor `δ_O + cyc κ_O` carries the other wall's detuning and carriers. It is close to
`δ_O · 1` when `|κ_O| ≪ |δ_O|`, and then the masses are `δ_O |κ_R(e g)|/|y|` and the left rotation
is small. The seesaw term `δ_F δ_T Y⁻¹` is absent, so the equal-carrier exclusion of
`tools/composite_mass_scan.py` (which assumed it) does not apply to this form.

With the swap × exchange symmetry (`LightSplit.light_split`), `κ_O(s) = κ_R(c)` and
`κ_O(c) = κ_R(s)`: the light ratio is `κ_R(s)/κ_R(c) = κ_R(s)/κ_O(s)`, one class's carrier on versus
off the reference's wall.
-/

noncomputable section
namespace PMFlavor.ReferenceWallMass
open Matrix PMFlavor.CyclicSeesaw PMFlavor.CompositeMass

/-- **With no detuning on the reference's wall the light mass factors as `D_R (δ_O + cyc κ_O)`.** -/
theorem reference_wall_mass (y κ κ' : Fin 3 → ℂ) (δT : ℂ) (hy : ∀ j, y j ≠ 0) :
    ((0 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) + cyc κ) * (cyc y)⁻¹ * (δT • 1 + cyc κ') =
      diagonal ![κ 2 * (y 2)⁻¹, κ 0 * (y 0)⁻¹, κ 1 * (y 1)⁻¹] * (δT • 1 + cyc κ') := by
  rw [zero_smul, zero_add, inv_cyc y hy, cyc_mul_cycInv]

end PMFlavor.ReferenceWallMass
