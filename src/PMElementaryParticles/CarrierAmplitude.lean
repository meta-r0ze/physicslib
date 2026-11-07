import PMElementaryParticles.CarrierSpecies
import PMConstants.CurrentConstants
import PMConstants.ElectroweakE8
import PMFlavor.CKM
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Carrier amplitudes from E8 couplings

A base-species amplitude slot with electromagnetic, weak and strong E8 couplings.
The assignment is a model input: electron/neutrino use the E8 electroweak
couplings; up/down additionally use the E8 CKM `Vud` and strong coupling.
-/

noncomputable section
namespace PMElementaryParticles.CarrierCouplings

open PMElementaryParticles.CarrierBridge

/-- Base-species amplitude slot. -/
structure CarrierAmplitude where
  em : ℝ
  weak : ℝ
  strong : ℝ

def alpha : ℝ := PMConstants.CurrentConstants.alpha
def weakCoupling : ℝ := PMConstants.ElectroweakE8.fermi alpha 1
def strongCoupling : ℝ := Real.sqrt PMConstants.CurrentConstants.strong
def vud : ℝ := PMFlavor.CKM.c12 * PMFlavor.CKM.c13

/-- E8 amplitude assignment for each base species. -/
def amplitude : CarrierSpecies → CarrierAmplitude
  | .electron => ⟨Real.sqrt alpha, weakCoupling, 0⟩
  | .neutrino => ⟨0, weakCoupling, 0⟩
  | .up => ⟨(2 / 3 : ℝ) * Real.sqrt alpha, weakCoupling * vud, strongCoupling⟩
  | .down => ⟨(-1 / 3 : ℝ) * Real.sqrt alpha, weakCoupling * vud, strongCoupling⟩

theorem neutrino_em_zero : (amplitude .neutrino).em = 0 := rfl

end PMElementaryParticles.CarrierCouplings
