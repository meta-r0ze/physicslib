import PMFlavor.Wolfenstein
import PMFlavor.CabibboDressing
import PMFlavor.PMNSIntervals
import PMFlavor.TriangleGamma
import PMFlavor.WolfensteinBar

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
* `cabibbo = s₁₂`, `ckmS13 = s₁₃`, `ckmS23 = s₂₃`; Wolfenstein `wolfLambda`, `wolfA`, and the barred `wolfRho = ρ̄`, `wolfEta = η̄` (PDG definition,
  `WolfensteinBar`; the paper's unbarred `ρ`, `η` are `wolfRhoPaper`, `wolfEtaPaper`);
  `ckmDeltaDeg` (`CPPhases.δdeg`), `sin2Beta`, `gammaDeg` (the triangle angles).
* PMNS: `pmnsSin2 j` (12, 23, 13), `pmnsEntry i j = |U_ij|²`, `pmnsJarlskog`.
* Re-exported facts: the angle bounds, Pythagorean identities, signs, `vus/vud = s₁₂/c₁₂`, and an
  enclosure for every value above.

e8p reads PMFlavor only through this module and compares these values with measurement.

**Readout names.** `vub = s₁₃` is the jump, the other-wall node crossing, and `vcb` the reference-wall
entry: `TransferGraph`'s naming, which the wire's masses with the derived carrier placement
(`PMAction.DetunedWire`) also give (lightest label `2`, middle `1`, heavy `0`; REVIEW item 0).
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


/-! ## Single source for e8p: further CKM, CP and PMNS values -/

/-- Cabibbo share `s₁₂ = π/14`. -/
abbrev cabibbo : ℝ := CKM.s12
/-- `s₁₃`. -/
abbrev ckmS13 : ℝ := CKM.s13
/-- `s₂₃`. -/
abbrev ckmS23 : ℝ := CKM.s23
/-- Wolfenstein `λ`. -/
abbrev wolfLambda : ℝ := Wolfenstein.wLam
/-- Wolfenstein `A`. -/
abbrev wolfA : ℝ := Wolfenstein.wA
/-- Wolfenstein `ρ̄`. -/
abbrev wolfRho : ℝ := WolfensteinBar.rhoBar
/-- Wolfenstein `η̄`. -/
abbrev wolfEta : ℝ := WolfensteinBar.etaBar
/-- The paper's unbarred `ρ` (`conj(V_ub)/(Aλ³)`), not the PDG `ρ̄`. -/
abbrev wolfRhoPaper : ℝ := Wolfenstein.wRho
/-- The paper's unbarred `η`. -/
abbrev wolfEtaPaper : ℝ := Wolfenstein.wEta
/-- The CKM phase in degrees. -/
abbrev ckmDeltaDeg : ℝ := CPPhases.δdeg
/-- `sin 2β` of the unitarity triangle. -/
abbrev sin2Beta : ℝ := TriangleAngles.sin2β
/-- The triangle angle `γ` in degrees. -/
abbrev gammaDeg : ℝ := TriangleGamma.value * 180 / Real.pi
/-- PMNS squared sines in 12, 23, 13 order. -/
abbrev pmnsSin2 (j : Fin 3) : ℝ := PMNS.sineSquared j
/-- PMNS squared moduli `|U_ij|²`. -/
abbrev pmnsEntry (i j : Fin 3) : ℝ := Complex.normSq (PMNS.matrix i j)
/-- The leptonic Jarlskog invariant. -/
abbrev pmnsJarlskog : ℝ := CKM.jarlskog PMNS.matrix

theorem cabibbo_bounds : (0.2243994 : ℝ) < cabibbo ∧ cabibbo < 0.2243995 := CKM.s12_bounds
theorem ckmS13_bounds : (0.0036073 : ℝ) < ckmS13 ∧ ckmS13 < 0.0036074 := CKM.s13_bounds
theorem ckmS23_bounds : (0.041308 : ℝ) < ckmS23 ∧ ckmS23 < 0.0413084 := CKM.s23_bounds
theorem wolfLambda_bounds : (0.22439 : ℝ) < wolfLambda ∧ wolfLambda < 0.22440 :=
  Wolfenstein.wLam_bounds
theorem wolfA_bounds : (0.8200 : ℝ) < wolfA ∧ wolfA < 0.8207 := WolfensteinBar.wA_tight
theorem wolfRho_bounds : (0.1411 : ℝ) < wolfRho ∧ wolfRho < 0.1412 := WolfensteinBar.rhoBar_bounds
theorem wolfEta_bounds : (0.3522 : ℝ) < wolfEta ∧ wolfEta < 0.3523 := WolfensteinBar.etaBar_bounds
theorem ckmDeltaDeg_bounds : (68.198 : ℝ) < ckmDeltaDeg ∧ ckmDeltaDeg < 68.201 :=
  CPPhases.δ_degrees
theorem sin2Beta_bounds : (0.7019 : ℝ) < sin2Beta ∧ sin2Beta < 0.7023 :=
  TriangleAngles.sin2β_bounds
theorem gammaDeg_bounds : (68.16 : ℝ) < gammaDeg ∧ gammaDeg < 68.17 := TriangleGamma.gamma_degrees
theorem pmnsSin2_bounds (j : Fin 3) :
    ![0.30901, 0.57479, 0.0218920] j < pmnsSin2 j ∧ pmnsSin2 j < ![0.30902, 0.57481, 0.0218921] j :=
  PMNSIntervals.input_bounds j
theorem pmnsEntry_bounds (i j : Fin 3) :
    PMNSIntervals.lower i j < pmnsEntry i j ∧ pmnsEntry i j < PMNSIntervals.upper i j :=
  PMNSIntervals.squared_entry_bounds i j
theorem pmnsJarlskog_bounds : (-0.0217 : ℝ) < pmnsJarlskog ∧ pmnsJarlskog < -0.0215 :=
  PMNSIntervals.jarlskog_bounds
theorem q2_eq : q2 = 515 / 516 := rfl

end PMFlavor.Values
