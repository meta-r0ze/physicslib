import PMConstants.TableConsequences
import PMSubstrate.Impedance
import PMFlavor.FlavourPostulates

/-!
# Paper IV's mixing formulas against PDG 2024 and NuFIT 6.0, and the shared weak mixing

This is the **measurement-comparison leaf**. The CKM/PMNS derivation modules import
`FlavourPostulates` (the `φ` postulate and numerical enclosures), not this file.
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

def αinv : ℝ := geometricIndex
def s12 : ℝ := Real.pi / 14
def s13 : ℝ := 1 / (2 * αinv + Real.pi)
def vus : ℝ := s12 * Real.sqrt (1 - s13 ^ 2)
def vcb : ℝ := (Real.pi + 2) / (αinv - 4 * Real.pi)
lemma g_b : (137.035999212 : ℝ) < αinv ∧ αinv < 137.035999213 := by
  have h := geometricIndex_bounds; constructor <;> unfold αinv <;> linarith [h.1, h.2]

lemma s13_b : (0.0036072 : ℝ) < s13 ∧ s13 < 0.0036074 := by
  have hp := pi_b; have hg := g_b
  have hd : 0 < 2 * αinv + Real.pi := by linarith
  unfold s13; constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

/-- **Paper IV's weak mixing is Paper III's.** -/
theorem weak_mixing_shared :
    (43 : ℝ) / (4 * 43 + 3 * Real.pi * PMConstants.overhead / (2 * s12) + (1 - PMConstants.overhead) * 5) =
      PMConstants.clockRatio ∧ PMConstants.clockRatio = 1849 / 8295 := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨?_, by norm_num [PMConstants.clockRatio, PMConstants.footprint, PMConstants.overhead]⟩
  unfold PMConstants.clockRatio PMConstants.footprint s12
  rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.RM_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq]
  congr 1
  field_simp
  ring

end PMFlavor.FlavourPulls
