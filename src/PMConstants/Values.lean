import PMConstants.CurrentConstants
import PMConstants.ElectroweakE8
import PMConstants.ElectroweakBounds
import PMConstants.JointConstants

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

end PMConstants.Values
