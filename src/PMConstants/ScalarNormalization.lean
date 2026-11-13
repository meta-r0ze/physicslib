import PMAction.ScalarTransport
import PMConstants.ChainCouplings
import PMConstants.LinkMass

/-!
# Scalar normalization from the event-priced D₄ chain

Paper II's `ScalarTransport` prices the scalar link by the same readout event as the gauge
plaquette and proves its continuum limit `Z_φ Σ_μ ‖(∂_μ + A_μ)Φ‖²` with `Z_φ = (3/4)·toll·m`
(`PMAction.ScalarTransport.scalar_limit`); the canonical field is `√Z_φ Φ`
(`scalar_canonical`). This replaces `EventStiffness.scalar_shares_prefactor`'s premise that the
scalar normalization follows from the same calibration with a continuum theorem.

* `scalar_z`: under `ChainCouplings.chain_calibration`, `Z_φ = 3/(8πα N_sys)`.
* `canonical_vev`: the canonical VEV is `v = √Z_φ · v_sub`, where `v_sub` is the substrate
  amplitude of the scalar's vacuum value.
* `w_mass_geometric`, `z_mass_geometric`: with the chain couplings
  (`ChainCouplings.chainCoupling`, charge-unit references) and `LinkMass`'s
  `m_W² = g²v²/4`, `m_Z² = (g² + g'²)v²/4`:
  `m_W² = (3/344)·v_sub²` and `m_Z² = (3/8)·N_sys/(43(N_sys − 43))·v_sub²`, independent of
  toll·m and α. The common prefactor cancels between the gauge and scalar terms.
* `mass_ratio`: `m_W²/m_Z² = 1 − clockRatio`, the tree-level `cos²θ_W`.

Premises (not derived): event pricing of scalar and gauge links with one repair length (one
toll is PM's cost definition, `PMSubstrate.NetCost`), the link weight `1/4` (each undirected link once per cell), summed charge-unit reads
for the couplings, cubic link consistency, and the substrate amplitude `v_sub` itself.
-/

noncomputable section
namespace PMConstants.ScalarNormalization
open PMAction ChainCouplings

/-- Scalar normalization of the chain. -/
def zPhi (toll : ℝ) (m : ℕ) : ℝ := 3 / 4 * (toll * m)

theorem scalar_z {toll α : ℝ} {m : ℕ} (hcal : toll * m = 1 / (2 * Real.pi * α * footprint)) :
    zPhi toll m = 3 / (8 * Real.pi * α * footprint) := by
  rw [zPhi, hcal]; field_simp; ring

/-- Canonical VEV from the substrate amplitude. -/
def canonicalVev (toll : ℝ) (m : ℕ) (vsub : ℝ) : ℝ := Real.sqrt (zPhi toll m) * vsub

theorem canonical_vev {toll : ℝ} {m : ℕ} (ht : 0 ≤ toll) (vsub : ℝ) :
    canonicalVev toll m vsub ^ 2 = zPhi toll m * vsub ^ 2 := by
  have : 0 ≤ zPhi toll m := by unfold zPhi; positivity
  rw [canonicalVev, mul_pow, Real.sq_sqrt this]

/-- **W mass in substrate units.** -/
theorem w_mass_geometric {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) (vsub : ℝ) :
    chainCoupling (1 / 2) toll m 43 * canonicalVev toll m vsub ^ 2 / 4 = 3 / 344 * vsub ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [canonical_vev ht.le]
  simp only [chainCoupling, zPhi]
  field_simp
  ring

/-- **Z mass in substrate units.** -/
theorem z_mass_geometric {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) (vsub : ℝ) :
    (chainCoupling (1 / 2) toll m 43 + chainCoupling (1 / 2) toll m (footprint - 43)) *
        canonicalVev toll m vsub ^ 2 / 4 =
      3 / 8 * (footprint / (43 * (footprint - 43))) * vsub ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := hf
  rw [canonical_vev ht.le]
  simp only [chainCoupling, zPhi]
  field_simp
  ring

/-- **Tree-level mass ratio** `m_W²/m_Z² = 1 − s`. -/
theorem mass_ratio {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) (vsub : ℝ) (hv : vsub ≠ 0) :
    (chainCoupling (1 / 2) toll m 43 * canonicalVev toll m vsub ^ 2 / 4) /
      ((chainCoupling (1 / 2) toll m 43 + chainCoupling (1 / 2) toll m (footprint - 43)) *
        canonicalVev toll m vsub ^ 2 / 4) = 1 - clockRatio := by
  rw [w_mass_geometric ht hm, z_mass_geometric ht hm]
  have := hf
  have := hfp
  have hv2 : vsub ^ 2 ≠ 0 := pow_ne_zero 2 hv
  simp only [clockRatio]
  rw [PMSubstrate.E8Values.Delta_eq]
  field_simp
  ring

/-- The `W` mass term of `LinkMass` with the canonical VEV is the chain's geometric value. -/
theorem link_mass_consistent {toll : ℝ} {m : ℕ} (ht : 0 < toll) (hm : 0 < m) (vsub : ℝ) :
    (Real.sqrt (chainCoupling (1 / 2) toll m 43)) ^ 2 * canonicalVev toll m vsub ^ 2 / 4 =
      3 / 344 * vsub ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hg : 0 ≤ chainCoupling (1 / 2) toll m 43 := by
    unfold chainCoupling; positivity
  rw [Real.sq_sqrt hg]
  exact w_mass_geometric ht hm vsub

end PMConstants.ScalarNormalization
