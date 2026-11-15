import PMFlavor.CKM
import PMFlavor.NodeElimination
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `|V_ub|` as the admittance of a two-leg series path

`|V_ub| = s₁₃ = 1/(χα⁻¹ + π)` (`CKM.s13`). The `2` is the two node legs of `NodeElimination`, the
degree of a class vertex in the generation–class incidence (`LinkKronComparison.two_leg_from_incidence`),
not an independent count.

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

**Why the product reading fails.** The leg product `t₁t₂ = α` with a unit denominator misses the
node's own conductance (`KronSeries.product_reading_wrong`).

**`|V_cb|` stays open.** The other node crossing is not given by this path; the comparison with data is
in `E8PConstants.CandidateTests.vcb_not_two_leg`.

**Which number this is.** The theorems here derive a path admittance; `vub_is_path` identifies it
with the *defined* `CKM.s13`. Whether the measured `|V_ub|` is that admittance depends on the
reading: in the transfer reading the path is the generator entry `K₁₃`, and the observable is
`|S₁₃|`, which also receives the route through the in-cycle pair.

The amplitude being the path's series admittance is derived in `KronSeries`: a conserving link is a
Laplacian, and eliminating the node (Kron reduction) gives exactly the series admittance. That the two legs are equal
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

end PMFlavor.VubSeriesPath
