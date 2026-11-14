import PMFlavor.Wolfenstein
import PMFlavor.CabibboDressing

/-!
# PMFlavor canonical values

Single source for the CKM magnitudes used by later libraries, mirroring
`PMSubstrate.E8Values` and `PMConstants.Values`. Downstream code (`PMElementaryParticles`,
`PMHadrons`, `e8p`) should import this module and use these names instead of writing
`c₁₂c₁₃` or `s₁₂c₁₃` again.

* `vud = c₁₂c₁₃`, `vus = s₁₂c₁₃`, `vub = s₁₃`, `vcb` — the standard-parametrization magnitudes
  with Paper IV's angles (`s₁₂ = π/14`, `s₁₃ = 1/(2α⁻¹+π)`).
* `q2 = 515/516`, `vudDressed = q·vud` — the Cabibbo dressing (`CabibboDressing`).
* `jarlskog = pmJ`, `jarlskogGeo = pm3J`.
* Re-exported facts: the angle bounds, Pythagorean identities, signs, `vus/vud = s₁₂/c₁₂`.
-/

noncomputable section
namespace PMFlavor.Values

/-- `|V_ud| = c₁₂ c₁₃`. -/
abbrev vud : ℝ := CKM.c12 * CKM.c13
/-- `|V_us| = s₁₂ c₁₃`. -/
abbrev vus : ℝ := CKM.s12 * CKM.c13
/-- `|V_ub| = s₁₃`. -/
abbrev vub : ℝ := CKM.s13
/-- `|V_cb|`. -/
abbrev vcb : ℝ := CKM.vcb
/-- Cabibbo dressing `q² = 515/516 = 1 − (1 − η)/(D − 1)`. -/
abbrev q2 : ℝ := CKMDressing.q2
/-- Dressed `|V_ud| = q·c₁₂c₁₃`. -/
abbrev vudDressed : ℝ := CabibboDressing.vudDressed
/-- CKM Jarlskog invariant (Paper IV). -/
abbrev jarlskog : ℝ := CKM.pmJ
/-- Paper III's geometric Jarlskog proposal. -/
abbrev jarlskogGeo : ℝ := CKM.pm3J

theorem s12_bounds : (0.2243994 : ℝ) < CKM.s12 ∧ CKM.s12 < 0.2243995 := CKM.s12_bounds
theorem s13_bounds : (0.0036073 : ℝ) < CKM.s13 ∧ CKM.s13 < 0.0036074 := CKM.s13_bounds
theorem c12_bounds : (0.974497 : ℝ) < CKM.c12 ∧ CKM.c12 < 0.974498 := CKM.c12_bounds
theorem c13_bounds : (0.999993 : ℝ) < CKM.c13 ∧ CKM.c13 ≤ 1 := CKM.c13_bounds
theorem c12_pyth : CKM.c12 ^ 2 + CKM.s12 ^ 2 = 1 := Wolfenstein.c12_pyth
theorem c13_pyth : CKM.c13 ^ 2 + CKM.s13 ^ 2 = 1 := Wolfenstein.c13_pyth
theorem c12_pos : 0 < CKM.c12 := Wolfenstein.c12_pos
theorem c13_pos : 0 < CKM.c13 := Wolfenstein.c13_pos

theorem vcb_bounds : (0.041308 : ℝ) < vcb ∧ vcb < 0.0413081 := CKM.vcb_bounds
theorem s23_bounds : (0.041308 : ℝ) < CKM.s23 ∧ CKM.s23 < 0.0413084 := CKM.s23_bounds

theorem jarlskog_bounds : (3.02e-5 : ℝ) < jarlskog ∧ jarlskog < 3.03e-5 := CKM.pmJ_bounds
theorem jarlskogGeo_bounds : (3.0848e-5 : ℝ) < jarlskogGeo ∧ jarlskogGeo < 3.0850e-5 :=
  CKM.pm3J_bounds

theorem vud_bounds : (0.974490 : ℝ) < vud ∧ vud < 0.974499 := CKM.vud_bounds
theorem vudDressed_bounds : (0.97354 : ℝ) < vudDressed ∧ vudDressed < 0.97357 :=
  CabibboDressing.vudDressed_bounds

/-- `c₁₃` cancels in the ratio: `|V_us|/|V_ud| = s₁₂/c₁₂ = tan θ₁₂`. -/
theorem vus_div_vud : vus / vud = CKM.s12 / CKM.c12 :=
  mul_div_mul_right _ _ c13_pos.ne'

end PMFlavor.Values
