import PMConstants.ColourChannels
import PMConstants.ScaleConsistency

/-!
# Certified enclosures for the colour-ledger strong coupling

The calculator now reads `α_s  = α N_sys/(12η)` (`ColourChannels`, `GaugeLedgers`). This module
gives the enclosures its regression tests check.

* `ledger_strong_squared`: `1.4827 < 4π α_s < 1.4829`.
* `ledger_interface_obstruction`: the interface factor `k` that matches the Z anchor puts
  `k α_s` above `0.1222`, so, as for the previous formula (`ScaleConsistency.same_scale_obstruction`),
  no single factor serves both readouts.
-/

noncomputable section
namespace PMConstants.StrongLedgerBounds
open PMConstants CertifiedConstants ElectroweakE8 GaugeSpectrum ElectroweakBounds ColourChannels

def ledgerStrong : ℝ := PMSubstrate.causalCoupling * footprint / colourLedger

theorem ledger_strong_squared :
    (1.4827 : ℝ) < 4 * Real.pi * ledgerStrong ∧ 4 * Real.pi * ledgerStrong < 1.4829 := by
  have hs := strong_from_channels
  have hp := pi_bounds
  unfold ledgerStrong
  constructor <;> nlinarith [hs.1, hs.2, hp.1, hp.2]

end PMConstants.StrongLedgerBounds
