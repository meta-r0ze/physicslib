import PMConstants.Values
import PMSubstrate.SIUnits
import PMSubstrate.Impedance
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Shared units and couplings

Constants used at every particle level (leptons, quarks, hadrons): the electron mass and `ħc`
unit inputs (CODATA 2022), Paper I's `α` and `α⁻¹` with their certified bounds, and `G_F` in
`m_e⁻²`. Split out of `PMHadrons.CompositeMasses` and `PMHadrons.NeutronRate` so the
elementary-particle level does not import the hadron level; those modules re-export them.
-/

noncomputable section
namespace PMElementaryParticles.SharedUnits
open PMSubstrate PMConstants

def αe : ℝ := PMConstants.Values.alpha
def αinv : ℝ := geometricIndex

/-- Electron mass in MeV (`PMSubstrate.SIUnits`, CODATA 2022). -/
def me : ℝ := PMSubstrate.SIUnits.electronMassMeV
/-- `ħc` in MeV·fm (`PMSubstrate.SIUnits`). -/
def hbarc : ℝ := PMSubstrate.SIUnits.hbarcMeVFm

lemma pi_b : (3.14159265358979323846 : ℝ) < Real.pi ∧ Real.pi < 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
lemma a_b : (0.007297352562 : ℝ) < αe ∧ αe < 0.007297352563 :=
  PMConstants.Values.alpha_bounds
lemma g_b : (137.035999212381397211 : ℝ) < αinv ∧ αinv < 137.035999212381397213 :=
  geometricIndex_bounds

/-- `G_F` in `m_e⁻²`. -/
def fermiME : ℝ :=
  Values.fermi Values.electronGeV *
    Values.electronGeV ^ 2

theorem fermiME_pos : 0 < fermiME := by
  have h := Values.fermi_bounds
  have he : 0 < Values.electronGeV ^ 2 := by
    unfold Values.electronGeV PMConstants.ElectroweakBounds.electronGeV PMSubstrate.SIUnits.electronMassGeV
    positivity
  unfold fermiME
  exact mul_pos (lt_trans (by norm_num) h.1) he

/-- `G_F` in `m_e⁻²` to about `2×10⁻⁶`: `3.0456453–3.0456507 × 10⁻¹²`. -/
theorem fermiME_tight : (3.0456453e-12 : ℝ) < fermiME ∧ fermiME < 3.0456507e-12 := by
  have h := Values.fermi_bounds
  have he : (2.611199276e-7 : ℝ) < Values.electronGeV ^ 2 ∧
      Values.electronGeV ^ 2 < (2.611199277e-7 : ℝ) := by
    unfold Values.electronGeV PMConstants.ElectroweakBounds.electronGeV PMSubstrate.SIUnits.electronMassGeV; norm_num
  unfold fermiME
  constructor <;> nlinarith [h.1, h.2, he.1, he.2]

end PMElementaryParticles.SharedUnits
