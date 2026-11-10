import PMHadrons.CompositeMasses
import PMElementaryParticles.Widths
import PMConstants.Values
import PMSubstrate.E8Values
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! **Continuum comparison.** This follows the usual continuum treatment; it is not an E8 assumption. The E8-native route is `PMElementaryParticles.BetaLattice`.


# Neutron beta width with a massive electron

The physical neutron channel is three-body:

```
n → p + e⁻ + ν̄
```

Unlike the muon, the electron is massive.  In the neutron rest frame and with
the proton recoil retained only through the endpoint, the phase-space integral is

```
f = ∫_{m_e}^{m_n−m_p} E √(E²−m_e²) (m_n−m_p−E)² dE
```

in `m_e = 1` units.  The V−A width is

```
Γ = G_F² |Vud|²/(2π³) · (1 + 3g_A²) · f.
```

`g_A = σ/D = 5/4` is the E8 axial assignment.  This module proves positivity and
the width/lifetime identities.  The numerical integral is comparison data, not a
theorem input.
-/

noncomputable section
namespace PMHadrons.NeutronRate
open PMElementaryParticles

open PMHadrons.CompositeMasses
open PMElementaryParticles.Widths
open PMConstants
export PMElementaryParticles.SharedUnits (fermiME fermiME_pos)

/-- Electron endpoint `m_n − m_p` in `m_e` units. -/
def endpoint : ℝ := neutron - proton

theorem endpoint_gt_one : 1 < endpoint := by
  have hp := proton_value
  have hn := neutron_value
  unfold endpoint
  linarith

/-- Massive-electron phase-space integrand. -/
def phaseIntegrand (E : ℝ) : ℝ :=
  E * Real.sqrt (E ^ 2 - 1) * (endpoint - E) ^ 2

theorem phaseIntegrand_continuous : Continuous phaseIntegrand := by
  unfold phaseIntegrand
  fun_prop

theorem phaseIntegrand_pos (E : ℝ) (h1 : 1 < E) (h2 : E < endpoint) :
    0 < phaseIntegrand E := by
  have hE : 0 < E := by linarith
  have hs : 0 < Real.sqrt (E ^ 2 - 1) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hd : 0 < endpoint - E := by linarith
  unfold phaseIntegrand
  positivity

/-- Massive-electron phase-space integral. -/
def phaseSpace : ℝ :=
  ∫ E in (1 : ℝ)..endpoint, phaseIntegrand E

theorem phaseSpace_pos : 0 < phaseSpace := by
  unfold phaseSpace
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (phaseIntegrand_continuous.intervalIntegrable _ _)
  · intro E hE
    exact phaseIntegrand_pos E hE.1 hE.2
  · exact endpoint_gt_one

/-- E8 axial assignment `g_A = σ/D = 5/4`. -/
def gA : ℝ := (PMSubstrate.E8Values.sigma : ℝ) / (PMSubstrate.E8Values.D : ℝ)

theorem gA_eq : gA = 5 / 4 := by
  unfold gA
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.D_eq]
  norm_num

/-- `1 + 3g_A²`, the V−A axial factor. -/
def axialFactor : ℝ := 1 + 3 * gA ^ 2

theorem axialFactor_eq : axialFactor = 91 / 16 := by
  unfold axialFactor
  rw [gA_eq]
  norm_num

theorem axialFactor_pos : 0 < axialFactor := by
  rw [axialFactor_eq]
  norm_num

/-- Neutron beta width for a supplied `Vud`. -/
def neutronWidth (Vud : ℝ) : ℝ :=
  (fermiME * Vud) ^ 2 / (2 * Real.pi ^ 3) * axialFactor * phaseSpace

theorem neutronWidth_eq (Vud : ℝ) :
    neutronWidth Vud =
      (fermiME * Vud) ^ 2 / (2 * Real.pi ^ 3) * axialFactor * phaseSpace := rfl

theorem neutronWidth_pos (Vud : ℝ) (hV : Vud ≠ 0) : 0 < neutronWidth Vud := by
  have hV2 : 0 < Vud ^ 2 := sq_pos_of_ne_zero hV
  have hG2 : 0 < (fermiME * Vud) ^ 2 := by
    rw [mul_pow]
    exact mul_pos (sq_pos_of_pos fermiME_pos) hV2
  have hden : 0 < 2 * Real.pi ^ 3 := by positivity
  unfold neutronWidth
  exact mul_pos (mul_pos (div_pos hG2 hden) axialFactor_pos) phaseSpace_pos

/-- Neutron mean life in `m_e⁻¹` units (`ħ = 1`). -/
def neutronLifetime (Vud : ℝ) : ℝ :=
  Widths.lifetime 1 (neutronWidth Vud)

theorem neutronLifetime_eq (Vud : ℝ) :
    neutronLifetime Vud = 1 / neutronWidth Vud := rfl

theorem neutronLifetime_pos (Vud : ℝ) (hV : Vud ≠ 0) : 0 < neutronLifetime Vud := by
  unfold neutronLifetime
  exact Widths.lifetime_pos (by norm_num) (neutronWidth_pos Vud hV)

/-- Paper V environmental factor `D = 215/213`. -/
def environmentFactor : ℝ := Widths.neutronFactor

theorem environmentFactor_eq : environmentFactor = 215 / 213 := by
  unfold environmentFactor Widths.neutronFactor
  norm_num

/-- Beam lifetime under the stated environmental rescaling. -/
def beamLifetime (Vud : ℝ) : ℝ := environmentFactor * neutronLifetime Vud

theorem beamLifetime_eq (Vud : ℝ) :
    beamLifetime Vud = environmentFactor * neutronLifetime Vud := rfl

end PMHadrons.NeutronRate

namespace PMHadrons.NeutronRate
open PMElementaryParticles

open PMHadrons.CompositeMasses
open PMElementaryParticles.Widths
open PMConstants

/-! ## Proton-recoil endpoint correction

The naive endpoint `m_n − m_p` ignores the proton recoil.  The exact maximum
electron total energy in the neutron rest frame is

```
E_rec = (m_n² + m_e² − m_p²)/(2 m_n).
```

Using `E_rec` in the phase-space integral retains the leading recoil effect;
the full angular Dalitz density and radiative corrections remain separate
inputs. -/

/-- Recoil-corrected electron endpoint, in `m_e` units. -/
def recoilEndpoint : ℝ :=
  (neutron ^ 2 + 1 - proton ^ 2) / (2 * neutron)

theorem recoilEndpoint_gt_one : 1 < recoilEndpoint := by
  have hp := proton_value
  have hn := neutron_value
  have h : proton < neutron - 1 := by linarith
  have hn0 : 0 < neutron := by linarith
  unfold recoilEndpoint
  rw [lt_div_iff₀ (by positivity : 0 < 2 * neutron)]
  nlinarith

theorem recoilEndpoint_lt_naive : recoilEndpoint < neutron - proton := by
  have hp := proton_value
  have hn := neutron_value
  have h : 1 < neutron - proton := by linarith
  have hn0 : 0 < neutron := by linarith
  unfold recoilEndpoint
  rw [div_lt_iff₀ (by positivity : 0 < 2 * neutron)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr h)]

/-- Recoil-corrected phase-space integrand. -/
def phaseIntegrandRecoil (E : ℝ) : ℝ :=
  E * Real.sqrt (E ^ 2 - 1) * (recoilEndpoint - E) ^ 2

theorem phaseIntegrandRecoil_continuous : Continuous phaseIntegrandRecoil := by
  unfold phaseIntegrandRecoil
  fun_prop

theorem phaseIntegrandRecoil_pos (E : ℝ) (h1 : 1 < E) (h2 : E < recoilEndpoint) :
    0 < phaseIntegrandRecoil E := by
  have hE : 0 < E := by linarith
  have hs : 0 < Real.sqrt (E ^ 2 - 1) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hd : 0 < recoilEndpoint - E := by linarith
  unfold phaseIntegrandRecoil
  positivity

/-- Recoil-corrected phase-space integral. -/
def phaseSpaceRecoil : ℝ :=
  ∫ E in (1 : ℝ)..recoilEndpoint, phaseIntegrandRecoil E

theorem phaseSpaceRecoil_pos : 0 < phaseSpaceRecoil := by
  unfold phaseSpaceRecoil
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (phaseIntegrandRecoil_continuous.intervalIntegrable _ _)
  · intro E hE
    exact phaseIntegrandRecoil_pos E hE.1 hE.2
  · exact recoilEndpoint_gt_one

/-- Recoil-corrected neutron width; `R` is the supplied radiative correction. -/
def neutronWidthRecoil (Vud R : ℝ) : ℝ :=
  R * (fermiME * Vud) ^ 2 / (2 * Real.pi ^ 3) * axialFactor * phaseSpaceRecoil

theorem neutronWidthRecoil_eq (Vud R : ℝ) :
    neutronWidthRecoil Vud R =
      R * (fermiME * Vud) ^ 2 / (2 * Real.pi ^ 3) * axialFactor * phaseSpaceRecoil := rfl

theorem neutronWidthRecoil_pos (Vud R : ℝ)
    (hV : Vud ≠ 0) (hR : 0 < R) : 0 < neutronWidthRecoil Vud R := by
  have hV2 : 0 < Vud ^ 2 := sq_pos_of_ne_zero hV
  have hG2 : 0 < (fermiME * Vud) ^ 2 := by
    rw [mul_pow]
    exact mul_pos (sq_pos_of_pos fermiME_pos) hV2
  have hden : 0 < 2 * Real.pi ^ 3 := by positivity
  unfold neutronWidthRecoil
  exact mul_pos (mul_pos (div_pos (mul_pos hR hG2) hden) axialFactor_pos) phaseSpaceRecoil_pos

/-- Recoil-corrected neutron mean life. -/
def neutronLifetimeRecoil (Vud R : ℝ) : ℝ :=
  Widths.lifetime 1 (neutronWidthRecoil Vud R)

theorem neutronLifetimeRecoil_eq (Vud R : ℝ) :
    neutronLifetimeRecoil Vud R = 1 / neutronWidthRecoil Vud R := rfl

theorem neutronLifetimeRecoil_pos (Vud R : ℝ)
    (hV : Vud ≠ 0) (hR : 0 < R) : 0 < neutronLifetimeRecoil Vud R := by
  unfold neutronLifetimeRecoil
  exact Widths.lifetime_pos (by norm_num) (neutronWidthRecoil_pos Vud R hV hR)

/-- Beam lifetime with the environmental factor. -/
def beamLifetimeRecoil (Vud R : ℝ) : ℝ :=
  environmentFactor * neutronLifetimeRecoil Vud R

end PMHadrons.NeutronRate
