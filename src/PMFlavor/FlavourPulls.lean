import PMConstants.TableConsequences
import PMSubstrate.Impedance
import PMFlavor.FlavourPostulates
import PMFlavor.CKM

/-!
# Paper IV's mixing formulas against PDG 2024 and NuFIT 6.0, and the shared weak mixing

The CKM values are `PMFlavor.Values` (`CKM.s12`, `s13`, `vcb`, …); this file no longer keeps its
own copies. The measured pulls are in e8p (`E8PConstants/PMFlavor/FlavourPulls`).
`α⁻¹` is Paper I's derived `geometricIndex`; `φ = (1 + √5)/2`.

**CKM** (PDG 2024):
* `vus_pull`: `|V_us| = s₁₂c₁₃`, `s₁₂ = π/(ν − χ)`, `s₁₃ = 1/(χα⁻¹ + π)`, within `0.2σ` of `0.22431(85)`.
* `vcb_pull`: `|V_cb| = (π + χ)/(α⁻¹ − Dπ)` within `0.2σ` of `0.0411(12)`.
* `vub_pull`: `|V_ub| = s₁₃` is `1.0–1.1σ` below `0.00382(20)`.

**PMNS** (NuFIT 6.0, as the calculator cites):
* `solar_pull`: `sin²θ₁₂ = 1/(2φ)` within `0.5σ` of `0.304(12)`.
* `atmos_pull`: `sin²θ₂₃ = (1 + π/(ν+σ))/χ` within `0.1σ` of `0.574(16)`.
* `reactor_pull`: `sin²θ₁₃ = (σ − χ)/α⁻¹` within `0.7σ` of `0.02225(56)`.

**The weak mixing is Paper III's.** Paper IV's impedance-matching form
`sin²θ_W = Δ/(DΔ + 3πη/(2 sin θ_C) + (1 − η)σ)` with `sin θ_C = s₁₂ = π/(ν − χ)` is exactly
Paper III's `Δ/N_sys = 1849/8295` (`weak_mixing_shared`), since `3πη/(2·π/14) + (1−η)σ = 16η + 5`.
-/

noncomputable section
namespace PMFlavor.FlavourPulls
open PMSubstrate

/-- **Paper IV's weak mixing is Paper III's.** -/
theorem weak_mixing_shared :
    (43 : ℝ) / (4 * 43 + 3 * Real.pi * PMConstants.overhead / (2 * PMFlavor.CKM.s12) + (1 - PMConstants.overhead) * 5) =
      PMConstants.clockRatio ∧ PMConstants.clockRatio = 1849 / 8295 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, by norm_num [PMConstants.clockRatio, PMConstants.footprint, PMConstants.overhead]⟩
  unfold PMConstants.clockRatio PMConstants.footprint PMFlavor.CKM.s12
  rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.RM_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq]
  congr 1
  field_simp
  ring

end PMFlavor.FlavourPulls
