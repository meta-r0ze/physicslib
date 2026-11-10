import PMConstants.Values
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

def me : ℝ := 0.51099895069
def hbarc : ℝ := 197.3269804

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
    unfold Values.electronGeV PMConstants.ElectroweakBounds.electronGeV
    positivity
  unfold fermiME
  exact mul_pos (lt_trans (by norm_num) h.1) he

end PMElementaryParticles.SharedUnits
