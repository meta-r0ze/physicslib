import PMAtoms.BetaLattice
import PersistenceMechanics.DecayChannel
import PersistenceMechanics.EffectiveAction
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! **Structural bridge.**

The finite-channel spectral weight is the squared modulus of the generic
coherent-action amplitude:

`betaSpectralWeight n a b c = |amplitude 0 1 λ(n,a,b,c)|²`.

Thus the finite spectral rate is a population/margin factor in the general
`DecayChannel` algebra, while `EffectiveAction.decoherenceRate` remains the
separate phase-loss channel.
-/

noncomputable section
namespace PMAtoms

open PersistenceMechanics
open PersistenceMechanics.EffectiveAction
open scoped BigOperators

/-- Fraction of the total spectral weight carried by `S`. -/
def spectralFraction (n : Nat) (S : Finset (Fin n × (Fin n × Fin n))) : ℝ :=
  betaSpectralRate 1 1 n S

theorem betaSpectralRate_eq_mul_fraction (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) :
    betaSpectralRate β c0 n S = β * c0 * spectralFraction n S := by
  unfold spectralFraction betaSpectralRate betaWeightedRate
  ring

/-- The generic decay channel whose margin is the finite spectral fraction. -/
def spectralDecayChannel (c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) : Decay.DecayChannel :=
  { capacity := 1
    map := 1
    protocol := 1
    governor := 1
    toll := c0
    margin := spectralFraction n S
    action := 0 }

theorem spectralDecayChannel_rate (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) :
    Decay.rate β (spectralDecayChannel c0 n S) = betaSpectralRate β c0 n S := by
  rw [betaSpectralRate_eq_mul_fraction]
  simp [Decay.rate, spectralDecayChannel]

/-- The population lifetime in the generic channel language. -/
def spectralLifetime (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) : ℝ :=
  1 / betaSpectralRate β c0 n S

theorem spectralDecayChannel_lifetime (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) :
    Decay.lifetime β (spectralDecayChannel c0 n S) = spectralLifetime β c0 n S := by
  unfold Decay.lifetime spectralLifetime
  rw [spectralDecayChannel_rate]

/-- The spectral rate as an `EffectiveAction` population width. -/
theorem betaSpectralRate_eq_effectiveWidth (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) :
    betaSpectralRate β c0 n S =
      EffectiveAction.width β (c0 * spectralFraction n S) 1 := by
  rw [betaSpectralRate_eq_mul_fraction]
  unfold EffectiveAction.width
  ring

/-- One spectral mode as a coherent-action amplitude. -/
def spectralAmplitude (n a b c : Nat) : ℂ :=
  EffectiveAction.amplitude 0 1 (dirichletEigenvalue n a b c)

/-- Spectral weight is exactly the squared modulus of the wave amplitude. -/
theorem betaSpectralWeight_eq_normSq_amplitude (n a b c : Nat) :
    betaSpectralWeight n a b c =
      Complex.normSq (spectralAmplitude n a b c) := by
  unfold betaSpectralWeight spectralAmplitude
  rw [EffectiveAction.amplitude_normSq]
  congr 1
  ring

/-- The mode-indexed amplitude used by the finite cube. -/
def spectralAmplitudeMode (n : Nat) (p : Fin n × (Fin n × Fin n)) : ℂ :=
  spectralAmplitude n (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1)

/-- The spectral rate is a normalized sum of wave probabilities. -/
theorem betaSpectralRate_eq_amplitude_probability (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) :
    betaSpectralRate β c0 n S =
      β * c0 * (S.sum (fun p => Complex.normSq (spectralAmplitudeMode n p))) /
        (Finset.univ.sum (fun p => Complex.normSq (spectralAmplitudeMode n p))) := by
  unfold betaSpectralRate betaWeightedRate
  simp only [betaSpectralWeight_eq_normSq_amplitude, spectralAmplitudeMode]

/-- Phase-loss rate, kept separate from the population width. -/
def spectralDecoherenceRate (β phaseCost time : ℝ) : ℝ :=
  EffectiveAction.decoherenceRate β phaseCost time

theorem spectralDecoherenceRate_eq (β phaseCost time : ℝ) :
    spectralDecoherenceRate β phaseCost time = β * phaseCost / time := rfl

end PMAtoms
