import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Flavour postulates and numerical enclosures

This module isolates the two numerical inputs that the derivation modules need:
the golden-ratio postulate `φ` and the certified enclosures for `π` and `√5`.
Measured PDG/NuFIT comparisons live in `E8PConstants.FlavourPulls`, which is **not**
imported by the CKM/PMNS derivation modules.

`φ` itself is now derived (`GoldenGeometry.pentagon_ratio_eq_phi`, `SixHundredCell`); the solar
form `1/(2φ)` that uses it is still supplied.
-/

noncomputable section
namespace PMFlavor.FlavourPulls

/-- The solar-sector postulate `φ = (1 + √5)/2`. -/
def φ : ℝ := (1 + Real.sqrt 5) / 2

lemma pi_b : (3.14159265358979 : ℝ) < Real.pi ∧ Real.pi < 3.1415926535898 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

lemma sqrt5_b : (2.2360679 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2360680 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg 5
  constructor <;> nlinarith

end PMFlavor.FlavourPulls
