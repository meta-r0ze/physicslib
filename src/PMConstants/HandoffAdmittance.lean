import PMConstants.DepthEvents
import PMSubstrate.ProtocolToll

/-!
# The handoff probability is the admittance `α`

`DepthEvents` derives the gravitational attenuation `α^{43/2}` from the event law, with one premise
left: the probability of the handoff event that carries a signal across one layer is the coupling
`α`. This module reduces that identification to two conventions the library already uses.

PM's `α` is an admittance: `α = 1/Z_geo`, the inverse of the node's impedance
(`PMSubstrate.causalCoupling`). `ProtocolToll` treats channels as Ohmic: admittances of parallel
channels add (`parallel_current`), and a unit admittance is one open channel
(`protocol_from_unit_channels`). Landauer's reading of a channel is the same: its dimensionless
conductance is its transmission probability, `G/G₀ = Σ Tᵢ`.

**Premise (transmission is admittance).** The probability that a layer passes the signal on is a
linear function of the layer's admittance (parallel channels add their transmissions), normalized
so that one unit-admittance channel passes it with certainty.

* `transmission_of_linear`: any such map is the identity, `T(y) = y`.
* `handoff_is_alpha`: so a layer of impedance `Z_geo` hands off with probability `1/Z_geo = α`.
* `attenuation_from_admittance`: crossing `n` layers has probability `α^n`
  (`DepthEvents.required_handoffs`), which is the input of `DepthEvents.gravity_from_events`.

Status: the identification `p = α` is replaced by "transmission is linear in admittance, unit
channel open", which is how the library already reads channels. Linearity is Landauer's
single-channel relation and holds for `T ≤ 1`; `α < 1` (`causalCoupling_bounds`). Not derived:
that a gravitational handoff is a channel of this kind. The residual factor `16 − 2/3 − α` is
unchanged.
-/

noncomputable section
namespace PMConstants.HandoffAdmittance
open PMConstants

/-- **A normalized linear transmission law is the identity.** -/
theorem transmission_of_linear (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) (y : ℝ) : T y = y := by
  have : T y = y • T 1 := by rw [← T.map_smul, smul_eq_mul, mul_one]
  rw [this, h1, smul_eq_mul, mul_one]

/-- **The handoff probability is `α`.** -/
theorem handoff_is_alpha (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) :
    T (1 / PMSubstrate.geometricIndex) = PMSubstrate.causalCoupling :=
  transmission_of_linear T h1 _

/-- The handoff probability is a probability. -/
theorem handoff_bounds (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) :
    0 < T (1 / PMSubstrate.geometricIndex) ∧ T (1 / PMSubstrate.geometricIndex) < 1 := by
  rw [handoff_is_alpha T h1]; exact PMSubstrate.causalCoupling_bounds

/-- **Attenuation over `n` layers is `α^n`.** -/
theorem attenuation_from_admittance (T : ℝ →ₗ[ℝ] ℝ) (h1 : T 1 = 1) (n : ℕ) :
    DepthEvents.crossProb (T (1 / PMSubstrate.geometricIndex)) n =
      PMSubstrate.causalCoupling ^ n := by
  rw [handoff_is_alpha T h1, DepthEvents.required_handoffs]

end PMConstants.HandoffAdmittance
