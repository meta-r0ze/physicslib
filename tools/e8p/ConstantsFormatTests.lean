import E8PConstants

/-! Kernel-evaluated formatter fixtures, including negative outward rounding. -/
open E8PConstants

example : fixedDecimal (-1) 3 = "-0.001" := by decide +kernel
example : fixedDecimal 0 3 = "0.000" := by decide +kernel
example : fixedDecimal 12001 3 = "12.001" := by decide +kernel
example : fixedDecimal (-12) 0 = "-12" := by decide +kernel
example : fixedDecimal (lowerScaled (-1/3) 3) 3 = "-0.334" := by decide +kernel
example : fixedDecimal (upperScaled (-1/3) 3) 3 = "-0.333" := by decide +kernel
example : fixedDecimal (lowerScaled (9999/1000) 2) 2 = "9.99" := by decide +kernel
example : fixedDecimal (upperScaled (9999/1000) 2) 2 = "10.00" := by decide +kernel
example : fixedDecimal (lowerScaled (-9999/1000) 2) 2 = "-10.00" := by decide +kernel
example : fixedDecimal (upperScaled (-9999/1000) 2) 2 = "-9.99" := by decide +kernel
example : fixedDecimal (lowerScaled (-1/3) 0) 0 = "-1" := by decide +kernel
example : fixedDecimal (upperScaled (-1/3) 0) 0 = "0" := by decide +kernel

-- χ² uses unrounded signed pulls, counts references, and has no reduced value for N = 0.
example : AuditStats.ofSigmas [-2, 1/2] = ⟨2, 17/4⟩ := by decide +kernel
example : (AuditStats.ofSigmas [-2, 1/2]).reduced = some (17/8) := by decide +kernel
example : (auditStats []).reduced = none := by decide +kernel
example : auditStats [.wMassUnc] = ⟨0, 0⟩ := by decide +kernel

-- Reference display preserves nonzero tiny lifetimes, errors and signed residuals.
example : comparisonNumber (8.43e-17) = "8.430000e-17" := by decide +kernel
example : comparisonNumber (-2.2e-12) = "-2.200000e-12" := by decide +kernel
example : comparisonNumber 0 = "0" := by decide +kernel
example : scoredRef .kaonFiniteLifetimeSeconds ⟨1, 1, "test"⟩ = false := by decide +kernel
