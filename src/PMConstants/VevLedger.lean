import PMConstants.VevCorrections
import PMConstants.ReferenceAnchor

/-! **VEV factor ledger.**

The VEV is written as four independent factors:

```
slot count × handoff × linear repair × margin × mass anchor.
```

This makes the remaining physical premises explicit instead of hiding them in
one formula.  The slot count is `χΔ² − (ν + DΔ)`, the handoff is `α⁻¹`, the
repair is first order (`1 + α/D_eff`), and the margin denominator is `σ−χ`, which
is also the number of axes orthogonal to the reference (`D−1`).
-/

noncomputable section
namespace PMConstants.VevLedger

open PMConstants ElectroweakE8 CertifiedConstants

/-- VEV slot count `χΔ² − (ν + DΔ)`. -/
def slotCount : ℝ :=
  (PMSubstrate.E8Values.chi : ℝ) * (PMSubstrate.E8Values.Delta : ℝ) ^ 2 -
    ((PMSubstrate.E8Values.nu : ℝ) +
      (PMSubstrate.E8Values.D : ℝ) * (PMSubstrate.E8Values.Delta : ℝ))

theorem slotCount_eq : slotCount = 3510 := by
  unfold slotCount
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
  norm_num

/-- Handoff factor `α⁻¹`. -/
def handoffFactor (α : ℝ) : ℝ := 1 / α

/-- First-order repair factor `1 + α/D_eff`. -/
def repairFactor (α : ℝ) : ℝ := 1 + α / effectiveDimension

/-- Margin factor `1 − Y/(σ−χ)`. -/
def marginFactor : ℝ :=
  1 - bareYukawa /
    ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ))

/-- The VEV as a factorised ledger. -/
def vevLedger (α me : ℝ) : ℝ :=
  slotCount * handoffFactor α * repairFactor α * marginFactor * me

theorem vevLedger_eq_vev (α me : ℝ) : vevLedger α me = vev α me := by
  unfold vevLedger slotCount handoffFactor repairFactor marginFactor vev vevRatio
  ring

/-- The noise denominator is exactly the number of axes orthogonal to the reference. -/
theorem noiseDenominator_eq_orthogonal :
    PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi =
      PMSubstrate.E8Values.D - 1 := by
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.D_eq]

/-- The boundary denominator is the `χ/(4π)` term. -/
theorem boundaryDenominator :
    (PMSubstrate.E8Values.chi : ℝ) /
        ((PMSubstrate.E8Values.D : ℝ) * Real.pi) =
      2 / (4 * Real.pi) := by
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.D_eq]
  norm_num

end PMConstants.VevLedger
