import PMElementaryParticles.CompositePhaseSpace

/-! **Hadronic matrix-element interface.**

The bound-state matrix element `⟨π⁺π⁰|T|K⁺⟩` is genuinely nonperturbative: the
current E8 library supplies the composite states, the carrier-product operator
form and the two-body phase space, but not the bound-state wavefunction overlap.
This module makes the missing object explicit instead of hiding it in a rate.

`HadronicMatrixElement.value` is a supplied complex input.  The rate consequence
is proved, but the value itself is not derived here.
-/

noncomputable section
namespace PMElementaryParticles.HadronicMatrixElement

open PMElementaryParticles.CompositeStates
open PMElementaryParticles.CompositeTransition
open PMElementaryParticles.CompositePhaseSpace
open PMElementaryParticles.CompositeMasses
open PMElementaryParticles.LeptonMasses

/-- A supplied bound-state matrix element. -/
structure BoundStateMatrixElement where
  initial : CompositeState
  final : List CompositeState
  value : ℂ
  provenance : String

/-- Two-body rate from a supplied bound-state matrix element. -/
def rate (M : BoundStateMatrixElement) (parent m1 m2 : ℝ) : ℝ :=
  Complex.normSq M.value * twoBodyPhaseSpace parent m1 m2

/-- The kaon/pion matrix element as an explicit input. -/
def kaonPion (value : ℂ) : BoundStateMatrixElement where
  initial := kaonPlus
  final := kaonPionFinal
  value := value
  provenance := "supplied bound-state overlap"

/-- Structural rate for `K⁺ → π⁺ π⁰` with a supplied matrix element. -/
def kaonPionRate (value : ℂ) : ℝ :=
  rate (kaonPion value) kaonPlus pionPlus pion0

theorem kaonPionRate_eq (value : ℂ) :
    kaonPionRate value = Complex.normSq value * kaonPionPhase := by
  simp [kaonPionRate, rate, kaonPion, kaonPionPhase]

theorem kaonPionRate_nonneg (value : ℂ) : 0 ≤ kaonPionRate value := by
  rw [kaonPionRate_eq]
  exact mul_nonneg (Complex.normSq_nonneg _) kaonPionPhase_pos.le

end PMElementaryParticles.HadronicMatrixElement
