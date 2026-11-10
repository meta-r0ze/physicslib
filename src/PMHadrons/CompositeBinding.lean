import PMHadrons.CompositePhaseSpace

/-! **Composite binding interface (comparison form).**

This writes a composite mass as "carrier sum minus binding energy". It is a
*comparison* ledger, not the E8 mass: on E8 a composite's mass is the occupancy
cost of its persistent configuration (`MesonMasses`). The binding energy here is
supplied, not derived from the substrate configuration.
-/

noncomputable section
namespace PMHadrons.CompositeBinding
open PMElementaryParticles

/-- Binding ledger for one composite state. -/
structure BindingLedger where
  constituentMassSq : ℝ
  bindingSq : ℝ

/-- Bound-state mass squared. -/
def compositeMassSq (B : BindingLedger) : ℝ :=
  B.constituentMassSq - B.bindingSq

theorem compositeMassSq_pos (B : BindingLedger)
    (h : B.bindingSq < B.constituentMassSq) : 0 < compositeMassSq B := by
  unfold compositeMassSq; linarith

/-- Binding lowers the mass. -/
theorem compositeMassSq_lt_constituent (B : BindingLedger)
    (h : 0 < B.bindingSq) : compositeMassSq B < B.constituentMassSq := by
  unfold compositeMassSq; linarith

/-- Phase space from the bound-state mass and two daughter masses. -/
def compositePhase (B : BindingLedger) (m1 m2 : ℝ) : ℝ :=
  PMHadrons.CompositePhaseSpace.twoBodyPhaseSpace
    (Real.sqrt (compositeMassSq B)) m1 m2

end PMHadrons.CompositeBinding
