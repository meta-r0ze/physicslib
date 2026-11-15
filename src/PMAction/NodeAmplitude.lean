import PMAction.KronReduction
import PMAction.ReferenceWallMass

/-!
# The node amplitude: a spinor-class carrier is `α/2` of the vector edge

`ReferenceWallMass`: every charged sector's light mass is `D_R (δ_O + cyc κ_O)`, and the light
carriers are spinor class with one magnitude `k` on both walls (one leg weight on both walls,
`PMConstants.HandoffAdmittance.closure_one_price`; the repair adds only a sign). This module fixes
`k` relative to the vector-class carrier `K` from the wire.

* The vector carrier is an in-cycle exchange (`ExchangeAxis.vector_free`): a gauge-repairable cycle
  event, which passes with certainty. Transmission is admittance normalized so a certain channel has
  admittance `1` (`HandoffAdmittance.transmission_of_linear`), so `K = 1`.
* The spinor carrier must cross the reference node (`ExchangeAxis.spinor_touch`): leg, node, leg,
  each leg of admittance `α` (`HandoffAdmittance.handoff_is_alpha`). The link conserves what it
  carries, so eliminating the node is Kron reduction (`PMAction.KronReduction.kron_two`): the two legs act in
  series.
* `node_series`, `node_kron`: so `k = 1/(1/α + 1/α) = α/2`, and `k/K = α/2`
  (`node_amplitude_value`: `1/(2Z)` with `Z = α⁻¹`).

The mass carrier stays on its wall, so no lead boundary enters. The CKM transfer between
generations does add one (`KronSeries.vub_from_kron`: the unit boundary `1/π` in series), so the
same node amplitude sets `|V_ub|` only with that boundary added.

Premises, all from the library: carrier amplitude is transmission is admittance
(`HandoffAdmittance`), the link is a Laplacian (Conservation, `KronSeries`), and an in-cycle event
transmits with certainty. How each species uses the wire is protocol work
(`PMElementaryParticles`).
-/

namespace PMAction.NodeAmplitude

/-- **Two node legs of admittance `α` in series give `α/2`.** -/
theorem node_series (α : ℝ) (_hα : 0 < α) : 1 / (1 / α + 1 / α) = α / 2 := by
  have h : (1 : ℝ) / α + 1 / α = 2 / α := by ring
  rw [h, one_div_div]

/-- **The same from Kron reduction of the node** (`PMAction.KronReduction.kron_two`). -/
theorem node_kron (α : ℝ) (hα : 0 < α) : (-α) * (-α) / (0 - (α + α)) = -(α / 2) := by
  rw [PMAction.KronReduction.kron_two α α hα hα, node_series α hα]

/-- **In units of the vector edge (`K = 1`), with `α = 1/Z`: `k = 1/(2Z)`.** -/
theorem node_amplitude_value (Z : ℝ) (hZ : 0 < Z) : 1 / (1 / (1 / Z) + 1 / (1 / Z)) = 1 / (2 * Z) := by
  rw [node_series (1 / Z) (by positivity)]; ring

end PMAction.NodeAmplitude
