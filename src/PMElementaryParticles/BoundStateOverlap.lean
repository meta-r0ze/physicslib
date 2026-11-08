import PMElementaryParticles.HadronicMatrixElement

/-! **Bound-state overlap interface.**

A bound-state matrix element is written as an inner product of two finite
constituent wavefunctions.  This supplies the missing structural object (the
overlap) without pretending that the wavefunction itself is derived.
-/

noncomputable section
namespace PMElementaryParticles.BoundStateOverlap

open PMElementaryParticles.CompositeStates

/-- A finite constituent wavefunction. -/
structure Wavefunction (ι : Type*) [Fintype ι] where
  amp : ι → ℂ

/-- Inner product of two wavefunctions. -/
def overlap {ι : Type*} [Fintype ι] (ψ φ : Wavefunction ι) : ℂ :=
  ∑ i, ψ.amp i * star (φ.amp i)

/-- Bound-state matrix element as an overlap. -/
def toMatrixElement {ι : Type*} [Fintype ι] (initial : CompositeState)
    (final : List CompositeState) (ψ φ : Wavefunction ι) : HadronicMatrixElement.BoundStateMatrixElement where
  initial := initial
  final := final
  value := overlap ψ φ
  provenance := "finite constituent overlap"

theorem rate_eq {ι : Type*} [Fintype ι] (initial : CompositeState)
    (final : List CompositeState) (ψ φ : Wavefunction ι) (parent m1 m2 : ℝ) :
    HadronicMatrixElement.rate (toMatrixElement initial final ψ φ) parent m1 m2 =
      Complex.normSq (overlap ψ φ) * PMElementaryParticles.CompositePhaseSpace.twoBodyPhaseSpace parent m1 m2 :=
  rfl

end PMElementaryParticles.BoundStateOverlap
