import PMConstants.CurrentConstants
import PMConstants.ElectroweakE8
import PMConstants.ElectroweakBounds
import PMConstants.JointConstants
import PMConstants.WMassTest
import PMConstants.GaugeLedgers
import PMConstants.GaugeSpectrum
import PMConstants.GaugeTraceNormalization
import PMConstants.GeneratorNormalization
import PMConstants.PlanckReadout
import PMConstants.GravityAccounting
import PMConstants.FloorNeutrino
import PMConstants.ColourChannels
import PMConstants.ContentWeight
import PMConstants.Depth
import PMConstants.Bulk
import PMConstants.ReadoutAccounting
import PMConstants.SharedReference
import PMConstants.TableConsequences
import PMConstants.ResourceLedger
import PMConstants.ScalarSector
import PMConstants.FermionMassLaw
import PMConstants.StrongLedgerTest
import PMConstants.Partition
import PMConstants.VevEntry
import PMConstants.VevCorrections
import PMConstants.WireMassBounds

/-!
# PMConstants canonical values

Single source for the dimensionless constants and derived electroweak quantities
used by later papers, mirroring `PMSubstrate.E8Values`. Downstream code should
import this module instead of reaching into `CertifiedConstants`,
`CurrentConstants`, `ElectroweakE8`, `ElectroweakBounds` or `JointConstants`
directly.

* `alpha`, `strong`, `weakFraction`, `scalar`, `electronYukawa` are the current
  manuscript values (`CurrentConstants`).
* `vev`, `higgsMass`, `fermi`, `weakSquared`, `hyperchargeSquared`,
  `strongSquared` are the `ElectroweakE8` allocation-law consequences evaluated
  on the canonical `alpha`.
* `electronGeV` is the dimensionful mass-unit anchor (experimental input).

The non-current formulas (`CertifiedConstants.strongCoupling`,
`ElectroweakE8.electronYukawa`) are deliberately **not** re-exported under these
names; keep using them only for regression/exclusion work.

Entry point: `Values.current_snapshot` for the dimensionless values, with the
individual `*_bounds` re-exported for direct use.

The second half of the module re-exports the gauge, gravity, readout and ledger names that `e8p`
reports, so the reporter reads this module alone and never a `PMConstants` internal.
-/

noncomputable section
namespace PMConstants.Values
open PMConstants

/-- Current fine-structure constant `α`. -/
abbrev alpha : ℝ := CurrentConstants.alpha
/-- Current strong coupling `α_s`. -/
abbrev strong : ℝ := CurrentConstants.strong
/-- Current on-shell weak fraction `sin²θ_W`. -/
abbrev weakFraction : ℝ := CurrentConstants.weakFraction
/-- Current scalar quartic `λ`. -/
abbrev scalar : ℝ := CurrentConstants.scalar
/-- Current electron Yukawa `y_e`. -/
abbrev electronYukawa : ℝ := CurrentConstants.electronYukawa

/-- Dimensionful electron-mass anchor in GeV (comparison input, not E8-derived). -/
abbrev electronGeV : ℝ := ElectroweakBounds.electronGeV

/-- The anchor as the substrate's SI electron mass, for unfolding downstream. -/
theorem electronGeV_eq : electronGeV = PMSubstrate.SIUnits.electronMassGeV := rfl

/-- VEV from the canonical `alpha`, in `me` units. -/
abbrev vev (me : ℝ) : ℝ := ElectroweakE8.vev alpha me
/-- Higgs mass from the canonical `alpha`, in `me` units. -/
abbrev higgsMass (me : ℝ) : ℝ := ElectroweakE8.higgsMass alpha me
/-- Fermi constant from the canonical `alpha`. -/
abbrev fermi (me : ℝ) : ℝ := ElectroweakE8.fermi alpha me
/-- Weak squared coupling `g_W²`. -/
abbrev weakSquared : ℝ := ElectroweakE8.weakSquared alpha
/-- Hypercharge squared coupling `g_Y²`. -/
abbrev hyperchargeSquared : ℝ := ElectroweakE8.hyperchargeSquared alpha
/-- Strong squared coupling `g_3²`. -/
abbrev strongSquared : ℝ := ElectroweakE8.strongSquared alpha

/-- The one checked entry point for the current dimensionless values. -/
alias current_snapshot := CurrentConstants.current_snapshot

alias alpha_bounds := CertifiedConstants.alpha_bounds
alias strong_bounds := CurrentConstants.strong_bounds
alias electron_bounds := CurrentConstants.electron_bounds

/-- Bounds for the derived electroweak quantities (from `ElectroweakBounds`),
re-exported so downstream papers depend on `Values` alone. -/
alias vev_bounds := ElectroweakBounds.vev_bounds
alias higgs_bounds := ElectroweakBounds.higgs_bounds
alias fermi_bounds := ElectroweakBounds.fermi_bounds
alias weak_squared_bounds := ElectroweakBounds.weak_squared_bounds
alias hypercharge_squared_bounds := ElectroweakBounds.hypercharge_squared_bounds
alias strong_squared_bounds := ElectroweakBounds.strong_squared_bounds
alias vev_ratio_bounds := JointConstants.vev_ratio_bounds

/-! ## Reported names

These are the `PMConstants` results `e8p` reports. They are re-exported here so the reporter
imports `Values` alone. -/

export PMConstants.ElectroweakBounds (coupling_bounds w_mass_bounds z_mass_bounds pi_bounds)
export PMConstants.ElectroweakE8 (vevRatio)
export PMConstants.WMassTest (wMass ratio_bounds)
export PMConstants.GaugeSpectrum (wMassSquared zMassSquared)
export PMConstants.GaugeLedgers (reqY ledger hyper_value)
export PMConstants.GaugeTraceNormalization (rawMixing raw_mixing_exact)
export PMConstants.GeneratorNormalization (mixing trace_form_gives_raw charge_units_give_effective)
export PMConstants.PlanckReadout (planckMass planckMass_bounds)
export PMConstants.JointConstants (electronClosureRatio electron_closure_bounds sqrt_two_bounds)
export PMConstants.GravityAccounting (residual_tight_bounds channels_as_frame)
export PMConstants.Depth (gravity)
export PMConstants.FloorNeutrino (floor_bounds meEV)
export PMConstants.Bulk (floorMass)
export PMConstants.ColourChannels (colourLedger colour_ledger strong_from_channels)
export PMConstants.ColourCount (root_count positive_roots link_triangles)
export PMConstants.GaugeStiffness (strongWorkload)
export PMConstants.ContentWeight (chi footprintW colourW extensive_w_mass extensive_strong)
export PMConstants.ReadoutAccounting (rawWMass selectedWeights)
export PMConstants.SharedReference (quarkWMass ReferenceLayout)
export PMConstants.TableConsequences (Premises)
export PMConstants.ResourceLedger (sterile_counted)
export PMConstants.ScalarSector (higgsSq higgs_from_fermi lambda_insensitive)
export PMConstants.FermionMassLaw (kappa_cost_light kappa_amp_light massA_event_priced)
export PMConstants (footprint overhead)
export PMConstants.CertifiedConstants (α)
export PMConstants.StrongLedgerTest (ledgerCoupling alpha_footprint_bounds ledger_twelve ledger_separation)
export PMAction.WallDispersion (massSqM rr)
export PMConstants.VevEntry (link_kappa_neg economy_law_A)
export PMConstants.VevCorrections (V Y x V_bounds Y_val x_bounds)
export PMConstants.WireMassBounds (bare_middle_heavy_bounds shifted_middle_heavy_bound kRate
  kRate_bounds rate_middle_heavy_bounds)

end PMConstants.Values
