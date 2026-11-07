import PMElementaryParticles.CarrierSpecies
import PMConstants.CurrentConstants
import PMConstants.ElectroweakE8
import PMFlavor.CKM
import PMAction.WeakVertex
import PMConstants.MatterRunning
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

/-- A two-species transition amplitude ledger. -/
structure CarrierTransition where
  source : CarrierSpecies
  target : CarrierSpecies

def CarrierTransition.em (t : CarrierTransition) : ℝ :=
  (amplitude t.source).em * (amplitude t.target).em

def CarrierTransition.weak (t : CarrierTransition) : ℝ :=
  (amplitude t.source).weak * (amplitude t.target).weak

def CarrierTransition.strong (t : CarrierTransition) : ℝ :=
  (amplitude t.source).strong * (amplitude t.target).strong

/-- Transition weight from the three E8 coupling channels. -/
def CarrierTransition.weight (t : CarrierTransition) : ℝ :=
  t.em ^ 2 + t.weak ^ 2 + t.strong ^ 2

/-- The weak carrier coupling equals the W-exchange Fermi coupling. -/
theorem weakCoupling_eq_fermi (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0)
    (hvev : v = PMConstants.ElectroweakE8.vev alpha 1) :
    weakCoupling = Real.sqrt 2 * (g ^ 2 / (8 * PMConstants.MatterRunning.mWsq g v)) := by
  rw [PMConstants.MatterRunning.fermi_from_reference g v hg hv]
  unfold weakCoupling PMConstants.ElectroweakE8.fermi
  rw [hvev]

end PMElementaryParticles.CarrierCouplings
