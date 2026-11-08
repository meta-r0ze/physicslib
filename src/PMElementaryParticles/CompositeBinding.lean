import PMElementaryParticles.CompositePhaseSpace

/-! **Composite binding interface.**

A composite mass is written as constituent mass minus binding energy.  This is a
structural ledger; the binding energy is supplied, not derived from a substrate
bound-state equation.
-/

noncomputable section
namespace PMElementaryParticles.CompositeBinding

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
  PMElementaryParticles.CompositePhaseSpace.twoBodyPhaseSpace
    (Real.sqrt (compositeMassSq B)) m1 m2

end PMElementaryParticles.CompositeBinding
