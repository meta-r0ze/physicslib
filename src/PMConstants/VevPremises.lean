import PMConstants.VevAccounting
import PMConstants.EventStiffness

/-!
# The VEV's two structural premises, made sharp

`VevAccounting` left two premises in the slot count and the handoff factor.

**Wires.** The footprint counts the wires `σ = 5` as per-phase work, but the VEV's slot count is
the node's boundary area `χΔ²` minus the node's own frame. Suppose each wire contributed a share
`s` of its weight to the node boundary (`s = 1/2` would split each wire between its two
endpoints). `wire_share_excluded`: every share `s ≥ 1/1000` puts the formula outside the Fermi
window. The data require the wires to carry no boundary weight. That is the geometric status of
a wire: it is a 1-cell between nodes, and a 1-cell meets a node's closed boundary surface only in
isolated points, so it occupies no boundary area. The wires are where the link field lives, not
part of the area it fills.

**Handoff.** `handoff_is_footprint_repair`: under the event calibration
`toll·m = 1/(4πα N_sys)` (`EventStiffness.calibration`), the handoff factor is exactly
`α⁻¹ = 4π · N_sys · (toll·m)`. Each interface slot costs one repair of the whole footprint,
read over the full solid angle, in units of the single repair that maintains the electron (the
Margin). This identity is exact. That the electron's maintenance is one repair is derived: the
electron is a singlet of colour and weak, so its repair is exactly one root event
(`RootRepairRule.electron_one_event`). The two correction factors remain.
-/

noncomputable section
namespace PMConstants.VevPremises
open PMConstants ElectroweakE8 CertifiedConstants ElectroweakBounds VevAccounting

theorem wire_share_excluded {GF s : ℝ} (h : 1.1663782e-5 < GF ∧ GF < 1.1663794e-5)
    (hs : 1/1000 ≤ s) :
    vevWith (188 + 5 * s) < Real.sqrt (1 / (Real.sqrt 2 * GF)) - 0.00008 := by
  have hw := fermi_window h
  have hv := vev_bounds
  have hpos : 0 < vev α electronGeV := by linarith [hv.1]
  unfold vevWith
  have e : (2 * 43^2 - (188 + 5 * s)) / 3510 = 1 - s / 702 := by ring
  rw [e]
  have : vev α electronGeV * (1 - s / 702) ≤ vev α electronGeV * (1 - (1/1000) / 702) := by
    apply mul_le_mul_of_nonneg_left _ hpos.le; linarith
  have h2 : vev α electronGeV * (1 - (1/1000) / 702) < 246.2196382 * (1 - (1/1000) / 702) := by
    apply mul_lt_mul_of_pos_right hv.2; norm_num
  linarith [hw.1]

theorem handoff_is_footprint_repair {toll : ℝ} {m : ℕ} (hα : 0 < α)
    (hcal : toll * m = 1 / (4 * Real.pi * α * footprint)) :
    1 / α = 4 * Real.pi * footprint * (toll * m) := by
  have hf : (0 : ℝ) < footprint := by norm_num [footprint, overhead]
  rw [hcal]; field_simp

end PMConstants.VevPremises
