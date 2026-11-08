import PMConstants.VevLedger
import PMConstants.VevPremises
import PMConstants.VevCorrections
import PMConstants.PersistenceClosures
import PMConstants.ReferenceDirections

/-! **VEV closure ledger.**

The VEV is now a fixed product of named factors.  Each factor is either closed
arithmetic, conditional on a named geometric/repair premise, or an explicit input.
This module composes the factor ledger into one theorem; it does not pretend that
the remaining premises are derived.
-/

noncomputable section
namespace PMConstants.VevClosure

open PMConstants ElectroweakE8 CertifiedConstants

/-- VEV factors in the order they enter the formula. -/
inductive VevFactor
  | slotCount
  | handoff
  | repair
  | boundary
  | margin
  | anchor

/-- Status of a VEV factor. -/
inductive VevStatus
  | closed
  | conditional
  | input
  deriving DecidableEq, Repr

/-- Status of each factor. -/
def factorStatus : VevFactor → VevStatus
  | .slotCount => .conditional
  | .handoff => .conditional
  | .repair => .conditional
  | .boundary => .conditional
  | .margin => .conditional
  | .anchor => .input

/-- The factorised VEV product. -/
def factorProduct (α me : ℝ) : ℝ :=
  VevLedger.slotCount * (1 / α) * (1 + α / effectiveDimension) *
    (1 - bareYukawa /
      ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ))) * me

/-- **VEV closure:** the current VEV is exactly the factor product. -/
theorem vev_closure (α me : ℝ) : vev α me = factorProduct α me := by
  rw [← VevLedger.vevLedger_eq_vev]
  unfold factorProduct VevLedger.vevLedger VevLedger.handoffFactor
    VevLedger.repairFactor VevLedger.marginFactor
  ring

/-- The slot count is the closed arithmetic part. -/
theorem slotCount_closed : VevLedger.slotCount = 3510 :=
  VevLedger.slotCount_eq

/-- The noise denominator is the reference-orthogonal axis count. -/
theorem noiseAxes_closed :
    PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi =
      PMSubstrate.E8Values.D - 1 :=
  VevLedger.noiseDenominator_eq_orthogonal

/-- The boundary denominator is the `χ/(4π)` term. -/
theorem boundary_closed :
    (PMSubstrate.E8Values.chi : ℝ) /
        ((PMSubstrate.E8Values.D : ℝ) * Real.pi) =
      2 / (4 * Real.pi) :=
  VevLedger.boundaryDenominator

/-- The one-repair count is the least positive repair count. -/
theorem oneRepair_closed : IsLeast {k : ℕ | 0 < k} 1 :=
  PersistenceClosures.one_repair

end PMConstants.VevClosure
