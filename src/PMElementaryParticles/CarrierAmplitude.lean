import PMElementaryParticles.CarrierSpecies
import PMConstants.Values
import PMFlavor.CKM
import PMAction.WeakVertex
import PMAction.AmplitudeTrace
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

def alpha : ℝ := PMConstants.Values.alpha
def weakCoupling : ℝ := PMConstants.Values.fermi 1
def strongCoupling : ℝ := Real.sqrt PMConstants.Values.strong
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
    (hvev : v = PMConstants.Values.vev 1) :
    weakCoupling = Real.sqrt 2 * (g ^ 2 / (8 * PMConstants.MatterRunning.mWsq g v)) := by
  rw [PMConstants.MatterRunning.fermi_from_reference g v hg hv]
  unfold weakCoupling PMConstants.Values.fermi
  rw [hvev]
  rfl

/-- Coherent transition amplitude ledger: sum of the three E8 coupling channels. -/
def CarrierTransition.amplitude (t : CarrierTransition) : ℝ :=
  t.em + t.weak + t.strong

theorem CarrierTransition.amplitude_eq (t : CarrierTransition) :
    t.amplitude = t.em + t.weak + t.strong := rfl

/-- Actual external-spinor contact matrix element from `PMAction`. -/
noncomputable def carrierMatrixElement (G : ℝ) {ιk ιp ιe ιb : Type*}
    [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
    (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ)
    (ue : ιe → Fin 4 → ℂ) (vb : ιb → Fin 4 → ℂ)
    (x : (ιk × ιp) × (ιe × ιb)) : ℂ :=
  PMAction.AmplitudeTrace.amp G uk up ue vb x

theorem carrierMatrixElement_eq_amp (G : ℝ) {ιk ιp ιe ιb : Type*}
    [Fintype ιk] [Fintype ιp] [Fintype ιe] [Fintype ιb]
    (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ)
    (ue : ιe → Fin 4 → ℂ) (vb : ιb → Fin 4 → ℂ)
    (x : (ιk × ιp) × (ιe × ιb)) :
    carrierMatrixElement G uk up ue vb x =
      PMAction.AmplitudeTrace.amp G uk up ue vb x := rfl

/-- Species-specific external spinors for one contact transition. -/
structure CarrierExternalStates where
  source : CarrierSpecies
  target : CarrierSpecies
  sourceSpinor : Fin 4 → ℂ
  targetSpinor : Fin 4 → ℂ
  electronSpinor : Fin 4 → ℂ
  neutrinoSpinor : Fin 4 → ℂ

/-- Contact matrix element from the species-specific external spinors. -/
noncomputable def CarrierExternalStates.matrixElement (G : ℝ)
    (s : CarrierExternalStates) : ℂ :=
  carrierMatrixElement G
    (fun _ : Fin 1 => s.sourceSpinor)
    (fun _ : Fin 1 => s.targetSpinor)
    (fun _ : Fin 1 => s.electronSpinor)
    (fun _ : Fin 1 => s.neutrinoSpinor)
    (((0 : Fin 1), (0 : Fin 1)), ((0 : Fin 1), (0 : Fin 1)))

/-- An on-shell carrier spinor: definite mass and energy. -/
structure CarrierSpinorState where
  species : CarrierSpecies
  energy : ℝ
  mass : ℝ
  spinor : Fin 4 → ℂ
  onShell : energy ^ 2 = mass ^ 2

/-- Four on-shell external spinors for a contact transition. -/
structure OnShellExternalStates where
  source : CarrierSpinorState
  target : CarrierSpinorState
  electron : CarrierSpinorState
  neutrino : CarrierSpinorState

/-- Contact matrix element from on-shell external spinors. -/
noncomputable def OnShellExternalStates.matrixElement (G : ℝ)
    (s : OnShellExternalStates) : ℂ :=
  carrierMatrixElement G
    (fun _ : Fin 1 => s.source.spinor)
    (fun _ : Fin 1 => s.target.spinor)
    (fun _ : Fin 1 => s.electron.spinor)
    (fun _ : Fin 1 => s.neutrino.spinor)
    (((0 : Fin 1), (0 : Fin 1)), ((0 : Fin 1), (0 : Fin 1)))

end PMElementaryParticles.CarrierCouplings
