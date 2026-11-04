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
