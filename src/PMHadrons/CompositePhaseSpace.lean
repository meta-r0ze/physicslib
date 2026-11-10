import PMHadrons.MesonMasses
import PMHadrons.CompositeTransition
import PMHadrons.CompositeMasses
import PMElementaryParticles.LeptonMasses

/-! **Composite two-body phase space.**

Standard two-body phase space for masses `M → m1 + m2`:

```
Φ₂ = √((M² − (m1+m2)²)(M² − (m1−m2)²)) / (8π M²).
```

The composite rate is `|T|² · Φ₂`.  The masses used for the kaon/pion instance are
the E8 composite-mass formulas; this is a structural rate instance, not a
numerical hadronic matrix element.
-/

noncomputable section
namespace PMHadrons.CompositePhaseSpace
open PMElementaryParticles

open PMHadrons.CompositeStates
open PMHadrons.CompositeTransition
open PMHadrons.CompositeMasses
open PMElementaryParticles.LeptonMasses
open PMHadrons.MesonMasses

/-- Two-body phase space for `M → m1 + m2`. -/
def twoBodyPhaseSpace (M m1 m2 : ℝ) : ℝ :=
  Real.sqrt ((M ^ 2 - (m1 + m2) ^ 2) * (M ^ 2 - (m1 - m2) ^ 2)) /
    (8 * Real.pi * M ^ 2)

theorem twoBodyPhaseSpace_pos {M m1 m2 : ℝ}
    (hM : 0 < M) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2) (h : m1 + m2 < M) :
    0 < twoBodyPhaseSpace M m1 m2 := by
  have hA : 0 < M ^ 2 - (m1 + m2) ^ 2 := by nlinarith
  have hB : 0 < M ^ 2 - (m1 - m2) ^ 2 := by nlinarith
  unfold twoBodyPhaseSpace
  positivity

/-- Composite partial width from an operator entry and two-body phase space. -/
def compositePartialWidth (T : ℂ) (M m1 m2 : ℝ) : ℝ :=
  Complex.normSq T * twoBodyPhaseSpace M m1 m2

/-- `K⁺ → π⁺ π⁰` operator entry. -/
def kaonPionT : ℂ :=
  compositeOperator kaonPlus kaonPionFinal

/-- `K⁺ → π⁺ π⁰` phase space from the E8 composite masses. -/
def kaonPionPhase : ℝ :=
  twoBodyPhaseSpace kaonPlus pionPlus pion0

/-- `K⁺ → π⁺ π⁰` structural partial width. -/
def kaonPionRate : ℝ := compositePartialWidth kaonPionT kaonPlus pionPlus pion0

theorem kaonPionRate_eq :
    kaonPionRate = Complex.normSq kaonPionT * kaonPionPhase := rfl

/-- The E8 composite masses put the kaon above the pion-pair threshold. -/
theorem kaonPionPhase_pos : 0 < kaonPionPhase := by
  have h1 := pionPlus_value
  have h2 := pion0_value
  have h3 := kaonPlus_value
  unfold kaonPionPhase
  apply twoBodyPhaseSpace_pos
  · linarith [h3.1]
  · linarith [h1.1]
  · linarith [h2.1]
  · linarith [h1.2, h2.2, h3.1]

theorem kaonPionRate_nonneg : 0 ≤ kaonPionRate := by
  rw [kaonPionRate_eq]
  exact mul_nonneg (Complex.normSq_nonneg _) kaonPionPhase_pos.le

end PMHadrons.CompositePhaseSpace
