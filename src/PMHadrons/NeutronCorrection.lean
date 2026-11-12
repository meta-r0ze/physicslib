import PMHadrons.DecayInstantiation
import Mathlib.Tactic

/-! **Candidate / comparison.**

# The neutron's own corrections in the semileptonic template

The one-template comparison (`DecayInstantiation`) leaves the neutron's +8.0% as four
neutron-only factors that the meson channels do not carry.  This module puts those
factors explicitly into the neutron rate:

* the outgoing electron's Coulomb attraction,
* the measured axial coupling against the E8 assignment `5/4`,
* the low-energy part of the radiative correction,
* the spectral-vs-continuum factor.

They are **supplied comparison inputs**, not E8 derivations; the E8 counterparts are
the open constructions in `PMHadrons.REVIEW-AND-NEXT` §0 (the cube's Green function,
the confined axial overlap and the radiative correction).  Multiplying the rate by
their product removes the 8% by construction and leaves the corrected E8 neutron
lifetime near the measured `878.4 s`.

Direction: the factors multiply the **rate**; the lifetime is divided by their
product.
-/

noncomputable section
namespace PMHadrons.NeutronCorrection

open PersistenceMechanics.Decay
open PMHadrons.DecayInstantiation

/-- Coulomb attraction of the outgoing electron: full phase space over the E8 endpoint. -/
def coulombCorrection : ℝ := 10322 / 10000

/-- Measured axial coupling against the E8 assignment: `(1+3g_A,meas²)/(1+3(5/4)²)`. -/
def axialCorrection : ℝ := 10338 / 10000

/-- Low-energy part of the radiative correction. -/
def radiativeCorrection : ℝ := 1018 / 1000

/-- Spectral-vs-continuum factor for the neutron channel. -/
def spectralCorrection : ℝ := 9941 / 10000

/-- Product of the four neutron-only factors. -/
def neutronOnlyCorrection : ℝ :=
  coulombCorrection * axialCorrection * radiativeCorrection * spectralCorrection

theorem coulombCorrection_eq : coulombCorrection = 1.0322 := by
  norm_num [coulombCorrection]

theorem axialCorrection_eq : axialCorrection = 1.0338 := by
  norm_num [axialCorrection]

theorem radiativeCorrection_eq : radiativeCorrection = 1.018 := by
  norm_num [radiativeCorrection]

theorem spectralCorrection_eq : spectralCorrection = 0.9941 := by
  norm_num [spectralCorrection]

theorem neutronOnlyCorrection_eq :
    neutronOnlyCorrection = 1.0322 * 1.0338 * 1.018 * 0.9941 := by
  norm_num [neutronOnlyCorrection, coulombCorrection, axialCorrection,
    radiativeCorrection, spectralCorrection]

theorem neutronOnlyCorrection_bounds :
    (1.07988 : ℝ) < neutronOnlyCorrection ∧ neutronOnlyCorrection < (1.07990 : ℝ) := by
  rw [neutronOnlyCorrection_eq]
  norm_num

theorem neutronOnlyCorrection_pos : 0 < neutronOnlyCorrection :=
  lt_trans (by norm_num) neutronOnlyCorrection_bounds.1

theorem neutronOnlyCorrection_gt_one : 1 < neutronOnlyCorrection :=
  lt_trans (by norm_num) neutronOnlyCorrection_bounds.1

/-- The neutron channel rate with the four neutron-only factors included. -/
def neutronCorrectedRate : ℝ := rate 1 neutronChannelCKM * neutronOnlyCorrection

/-- The neutron lifetime in seconds with the four neutron-only factors included. -/
def neutronCorrectedLifetimeSeconds : ℝ :=
  neutronLifetimeUnifiedSeconds / neutronOnlyCorrection

/-- The corrected lifetime is the uncorrected one divided by the supplied factor. -/
theorem neutronCorrectedLifetimeSeconds_eq :
    neutronCorrectedLifetimeSeconds =
      neutronLifetimeUnifiedSeconds / neutronOnlyCorrection := rfl

/-- The corrected rate gives the corrected lifetime: `1/Γ · electronTime`. -/
theorem neutronCorrectedLifetimeSeconds_eq_correctedRate :
    neutronCorrectedLifetimeSeconds =
      (1 / neutronCorrectedRate) * PMElementaryParticles.PhysicalUnits.electronTime := by
  unfold neutronCorrectedLifetimeSeconds neutronCorrectedRate neutronLifetimeUnifiedSeconds
  rw [neutronChannelCKM_rate]
  unfold neutronLifetimeExactCutoff betaLifetimeFromFraction
  field_simp

/-- **With the supplied neutron-only factors, the E8 neutron lifetime is between `878.50` and
`878.52` s.** -/
theorem neutronCorrectedLifetimeSeconds_bounds :
    (878.50 : ℝ) < neutronCorrectedLifetimeSeconds ∧
      neutronCorrectedLifetimeSeconds < (878.52 : ℝ) := by
  have h := neutronLifetimeUnifiedSeconds_bounds
  have hc : 0 < neutronOnlyCorrection := neutronOnlyCorrection_pos
  have h1 : (878.50 : ℝ) * neutronOnlyCorrection < (948.69 : ℝ) := by
    rw [neutronOnlyCorrection_eq]
    norm_num
  have h2 : (948.70 : ℝ) < (878.52 : ℝ) * neutronOnlyCorrection := by
    rw [neutronOnlyCorrection_eq]
    norm_num
  unfold neutronCorrectedLifetimeSeconds
  constructor
  · rw [lt_div_iff₀ hc]
    nlinarith [h.1, h1]
  · rw [div_lt_iff₀ hc]
    nlinarith [h.2, h2]

/-- The corrected lifetime in the uncorrected channel's units (`m_e⁻¹`). -/
def neutronCorrectedLifetime : ℝ :=
  neutronLifetimeUnifiedSeconds / neutronOnlyCorrection /
    PMElementaryParticles.PhysicalUnits.electronTime

theorem neutronCorrectedLifetime_pos : 0 < neutronCorrectedLifetime := by
  unfold neutronCorrectedLifetime
  have h1 : 0 < neutronLifetimeUnifiedSeconds := by
    have h := neutronLifetimeUnifiedSeconds_bounds
    linarith [h.1]
  have h2 : 0 < neutronOnlyCorrection := neutronOnlyCorrection_pos
  have h3 : 0 < PMElementaryParticles.PhysicalUnits.electronTime :=
    PMElementaryParticles.PhysicalUnits.electronTime_pos
  positivity

end PMHadrons.NeutronCorrection
