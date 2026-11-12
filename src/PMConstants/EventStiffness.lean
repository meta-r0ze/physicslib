import PMAction.EventCoupling
import PMAction.CommonResponse
import PMConstants.GaugeLedgers

/-!
# Gauge stiffness from Paper II's event law

`GaugeStiffness` took as its premise that each refresh of a sector's links pays the local
curvature cost at a common toll `c₀`, so `β = c₀W`. Paper II connects that cost to E8 carrier events under its stated preparation,
squared-amplitude readout and common repair-length contracts
(`PMAction.CarrierResponse`, `PMAction.CommonResponse`).

* `refresh_from_events`: `W` refreshes of a phase test, each a flag readout repaired by `m`
  primitive events at the common toll, cost `(c₀W)(1 − cos θ)` with `c₀ = toll·m/2`. This is
  `GaugeStiffness.refresh_ledger` with `S = 1 − cos θ`; its phase dependence follows under those contracts; W remains supplied.
* `coupling_from_events`: `g² = 1/(2c₀W) = 1/(toll·m·W)`.
* `calibration`: the electric coupling is the footprint's, `e² = 1/(toll·m·N_sys)`
  (`GaugeLedgers.footprint_from_rule`). Setting `e² = 4πα` with Paper I's `α` fixes the one
  remaining product, `toll·m = 1/(4πα N_sys)`.
* `couplings_from_alpha`: given the specified gauge resource ledgers and calibration:
  `g_W² = 4πα N_sys/43`, `g_Y² = 4πα N_sys/(129 + 5 + 16η)`, `g_3² = 4πα N_sys/(12η)`.
* `scalar_shares_prefactor`: if the scalar link is priced by the same readout event as the gauge
  plaquette (`CommonResponse.responseCost`, same toll and repair length `m`), both have prefactor
  `toll·m/4` and the scalar normalization follows from the same calibration. The shared prefactor
  is that pricing premise (`CommonResponse.common_normalization` only factors it out); it is not
  derived from the carrier events.

What remains outside this chain: the repair length `m` as a Paper II input (only its product
with the toll enters, and the chosen electric calibration fixes it; the squared-amplitude readout
is now derived, `PMAction.ReadoutRule.born`),
the resource/refresh weights W, and the matching of the lattice couplings to measured ones
at a stated scale. ColourPhaseMaintenance supplies an exact three-axis response
interpretation of the conditional colour factor 12η; it does not derive η or its cadence.
-/

noncomputable section
namespace PMConstants.EventStiffness
open PMConstants PMAction

export PMAction.EventCoupling (c0 refresh_from_events coupling_from_events
  scalar_shares_prefactor)

theorem matches_refresh_ledger (toll θ : ℝ) (m W : ℕ) :
    (∑ _ : Fin W, CarrierResponse.repairCost toll m (InterferenceReadout.phase θ)) =
      ∑ _ : Fin W, c0 toll m * (1 - Real.cos θ) := by
  rw [refresh_from_events, GaugeStiffness.refresh_ledger]

theorem calibration {toll α : ℝ} {m : ℕ} (hα : 0 < α)
    (he : GaugeStiffness.gsq (c0 toll m * footprint) = 4 * Real.pi * α) :
    toll * m = 1 / (4 * Real.pi * α * footprint) := by
  rw [coupling_from_events] at he
  have hf : (0 : ℝ) < footprint := by norm_num [footprint, overhead]
  have hp : 0 < 4 * Real.pi * α * footprint := by positivity
  have h4 : 0 < 4 * Real.pi * α := by positivity
  have hne : toll * m * footprint ≠ 0 := by
    intro h0; rw [h0, div_zero] at he; linarith
  have k : (toll * m * footprint) * (4 * Real.pi * α) = 1 := by
    have htm : toll * (m : ℝ) ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
    rw [← he]; field_simp; exact div_self htm
  rw [eq_div_iff hp.ne']
  linear_combination k

theorem couplings_from_alpha {toll α : ℝ} {m : ℕ} (hα : 0 < α)
    (hcal : toll * m = 1 / (4 * Real.pi * α * footprint)) :
    GaugeStiffness.gsq (c0 toll m * GaugeLedgers.ledger GaugeLedgers.reqSU2) =
        4 * Real.pi * α * footprint / 43 ∧
      GaugeStiffness.gsq (c0 toll m * GaugeLedgers.ledger GaugeLedgers.reqY) =
        4 * Real.pi * α * footprint / (129 + 5 + 16 * overhead) ∧
      GaugeStiffness.gsq (c0 toll m * GaugeLedgers.ledger GaugeLedgers.reqColour) =
        4 * Real.pi * α * footprint / ColourChannels.colourLedger := by
  rw [GaugeLedgers.su2_value, GaugeLedgers.hyper_value, GaugeLedgers.colour_value]
  simp only [coupling_from_events, hcal]
  have hf : (0 : ℝ) < footprint := by norm_num [footprint, overhead]
  have hc : (0 : ℝ) < ColourChannels.colourLedger := by
    rw [ColourChannels.colour_ledger]; norm_num
  have hy : (0 : ℝ) < 129 + 5 + 16 * overhead := by norm_num [overhead]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

end PMConstants.EventStiffness
