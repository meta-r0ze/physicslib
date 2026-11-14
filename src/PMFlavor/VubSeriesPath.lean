import PMFlavor.MixingTests
import PMFlavor.NodeElimination

/-!
# `|V_ub|` as the admittance of a two-leg series path

`|V_ub| = s₁₃ = 1/(χα⁻¹ + π)` (`CKM.s13`). Among `1/(m Z_geo)` the data fix `m = 2`
(`MixingTests.vub_count_unique`). This module reads the `2` as the two node legs of
`NodeElimination` rather than as an independent count.

**Construction.** The two node-crossing quark mixings pass the reference node (`ExchangeAxis`):
in through the node and back out, two legs (`NodeElimination.two_legs`), each of impedance
`Z_geo = α⁻¹` (`PMSubstrate.causalCoupling`). Impedances in series add (Ohm,
`PMSubstrate.ProtocolToll`, as in `PMConstants.VevImpedance.series`), and a boundary of unit width
adds its length `π` (Barbier, `PMSubstrate.Capacity.barbier`; the same boundary as
`PMConstants.VevBoundary`). The transfer amplitude of the path is its admittance:
* `path_admittance`: `1/(Z + Z + π) = 1/(2Z + π)`;
* `vub_is_path`: with `Z = α⁻¹` this is exactly `CKM.s13`.
* `as_node_elimination`: in `NodeElimination` units (`α = 1/Z`) the same amplitude is
  `α/(2 + πα)`: the energy denominator `e − E` left open there is the impedance of the legs and
  boundary, `2 + πα` in units of `Z`, not `1`.

**Why the product reading fails.** The leg product `t₁t₂ = α` with a unit denominator is `1/Z`,
the `m = 1` member, which `vub_count_unique` excludes (`m = 2` only). The series path gives the
data's `m = 2` without a separate count.

**What the data do not fix.** The boundary term: `1/(2Z)` and `1/(2Z + π)` differ by `1%`, below the
error on `|V_ub|` (`boundary_unresolved`). It rests on the construction.

Premise: the mixing amplitude of a passive path is its admittance (the transfer per unit drive, as
`HandoffAdmittance` reads a node's through weight as its conductance). That the two legs are equal
is Closure (`HandoffAdmittance.closure_one_price`).
-/

namespace PMFlavor.VubSeriesPath

/-- Admittance of impedances in series. -/
noncomputable def seriesAdmittance (zs : List ℝ) : ℝ := 1 / zs.sum

theorem path_admittance (Z : ℝ) : seriesAdmittance [Z, Z, Real.pi] = 1 / (2 * Z + Real.pi) := by
  simp only [seriesAdmittance, List.sum_cons, List.sum_nil, add_zero]
  congr 1; ring

theorem vub_is_path : seriesAdmittance [CKM.αinv, CKM.αinv, Real.pi] = CKM.s13 := by
  rw [path_admittance]; rfl

theorem as_node_elimination (Z : ℝ) (hZ : 0 < Z) :
    1 / (2 * Z + Real.pi) = (1 / Z) / (2 + Real.pi * (1 / Z)) := by
  have hp := Real.pi_pos
  field_simp

theorem boundary_unresolved :
    |(1 / (2 * 137.036) : ℝ) - 0.00382| / 0.0002 < 2 ∧
      |(1 / (2 * 137.036 + 3.1416) : ℝ) - 0.00382| / 0.0002 < 2 := by
  constructor <;> (rw [abs_of_neg (by norm_num)]; norm_num)

end PMFlavor.VubSeriesPath
