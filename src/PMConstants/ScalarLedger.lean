import PMConstants.ScalarBudget
import PMConstants.ScalarSector

/-! **Scalar factor ledger.**

The scalar gain is written as

```
λ = (B − 1/Δ)/(ν+σ+χ),
```

with budget `B = σ−χ = 3`, clock credit `1/Δ`, and `ν+σ+χ = 23` labels.  The
toll is `T = 2λ` and the mass term is `μ² = λ v²`.  The budget count is selected
by the scalar window; which substrate reading supplies it remains a premise.
-/

noncomputable section
namespace PMConstants.ScalarLedger

open PMConstants

/-- Scalar budget `B = σ−χ`. -/
def scalarBudget : ℕ :=
  PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi

theorem scalarBudget_eq : scalarBudget = 3 := by
  norm_num [scalarBudget, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq]

/-- Scalar label count `ν+σ+χ`. -/
def scalarLabels : ℕ :=
  PMSubstrate.E8Values.nu + PMSubstrate.E8Values.sigma + PMSubstrate.E8Values.chi

theorem scalarLabels_eq : scalarLabels = 23 := by
  norm_num [scalarLabels, PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.chi_eq]

/-- Clock credit `1/Δ`. -/
def clockCredit : ℝ := 1 / (PMSubstrate.E8Values.Delta : ℝ)

/-- Scalar gain ledger. -/
def scalarGain : ℝ := ((scalarBudget : ℝ) - clockCredit) / (scalarLabels : ℝ)

theorem scalarGain_eq : scalarGain = selfCoupling := by
  unfold scalarGain scalarBudget scalarLabels clockCredit selfCoupling
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num

/-- Ledger toll `T = 2λ`. -/
def scalarTollLedger : ℝ := 2 * scalarGain

theorem scalarTollLedger_eq : scalarTollLedger = scalarToll := by
  rw [scalarTollLedger, scalarGain_eq]
  rfl

/-- Ledger mass term `μ² = λv²`. -/
def scalarMassSq (v : ℝ) : ℝ := scalarGain * v ^ 2

theorem scalarMassSq_eq (v : ℝ) : scalarMassSq v = selfCoupling * v ^ 2 := by
  rw [scalarMassSq, scalarGain_eq]

/-- The budget is the colour-bulk dimension. -/
theorem scalarBudget_eq_colourBulk :
    scalarBudget = PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi := rfl

end PMConstants.ScalarLedger
