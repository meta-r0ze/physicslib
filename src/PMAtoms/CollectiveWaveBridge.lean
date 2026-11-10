import PMAtoms.CollectiveFinite
import PMAtoms.SpectralWaveBridge
import PersistenceMechanics.DecayChannel
import PersistenceMechanics.EffectiveAction
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! **Collective barrier ↔ wave/decay bridge.**

The finite collective rate is a normalized barrier-weight population rate.  It
is the alpha/fission analogue of `SpectralWaveBridge`: barrier weight is the
squared modulus of the coherent-action amplitude, and the phase-loss channel is
kept separate with an explicit model-input phase cost.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

open PersistenceMechanics
open PersistenceMechanics.EffectiveAction
open scoped BigOperators

/-- Fraction of the total barrier weight carried by `S`. -/
def collectiveFraction {k : Nat} (barriers : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  collectiveFiniteRate 1 1 barriers S

theorem collectiveFiniteRate_eq_mul_fraction (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) :
    collectiveFiniteRate β c0 barriers S = β * c0 * collectiveFraction barriers S := by
  unfold collectiveFraction collectiveFiniteRate
  ring

/-- Generic decay channel whose margin is the finite collective fraction. -/
def collectiveDecayChannel (c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) : Decay.DecayChannel :=
  { capacity := 1
    map := 1
    protocol := 1
    governor := 1
    toll := c0
    margin := collectiveFraction barriers S
    action := 0 }

theorem collectiveDecayChannel_rate (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) :
    Decay.rate β (collectiveDecayChannel c0 barriers S) =
      collectiveFiniteRate β c0 barriers S := by
  rw [collectiveFiniteRate_eq_mul_fraction]
  simp [Decay.rate, collectiveDecayChannel]

/-- Collective population lifetime. -/
def collectiveLifetime (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  1 / collectiveFiniteRate β c0 barriers S

theorem collectiveDecayChannel_lifetime (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) :
    Decay.lifetime β (collectiveDecayChannel c0 barriers S) =
      collectiveLifetime β c0 barriers S := by
  unfold Decay.lifetime collectiveLifetime
  rw [collectiveDecayChannel_rate]

/-- Collective rate as an `EffectiveAction` population width. -/
theorem collectiveFiniteRate_eq_effectiveWidth (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) :
    collectiveFiniteRate β c0 barriers S =
      EffectiveAction.width β (c0 * collectiveFraction barriers S) 1 := by
  rw [collectiveFiniteRate_eq_mul_fraction]
  unfold EffectiveAction.width
  ring

/-- One collective barrier as a coherent-action amplitude. -/
def collectiveAmplitude (barrier : ℝ) : ℂ :=
  EffectiveAction.amplitude 0 1 barrier

theorem collectiveBarrierWeight_eq_normSq_amplitude (barrier : ℝ) :
    collectiveBarrierWeight barrier =
      Complex.normSq (collectiveAmplitude barrier) := by
  unfold collectiveBarrierWeight collectiveAmplitude
  rw [EffectiveAction.amplitude_normSq]
  congr 1
  ring

/-- Collective rate as a normalized sum of wave probabilities. -/
theorem collectiveFiniteRate_eq_amplitude_probability (β c0 : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) :
    collectiveFiniteRate β c0 barriers S =
      β * c0 * (S.sum (fun i => Complex.normSq (collectiveAmplitude (barriers i)))) /
        (Finset.univ.sum (fun i => Complex.normSq (collectiveAmplitude (barriers i)))) := by
  unfold collectiveFiniteRate
  simp only [collectiveBarrierWeight_eq_normSq_amplitude]

/-- One proposed collective phase-cost rule: the barrier-weight average.  This
is an explicit model input, not a population rate. -/
def collectiveMeanBarrier {k : Nat} (barriers : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  (S.sum (fun i => barriers i * collectiveBarrierWeight (barriers i))) /
    (S.sum (fun i => collectiveBarrierWeight (barriers i)))

/-- Phase-loss channel for a finite collective barrier set. -/
def collectiveDecoherenceChannel {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) : SpectralDecoherenceChannel :=
  { phaseCost := collectiveMeanBarrier barriers S
    time := 1 }

theorem collectiveDecoherenceChannel_rate (β : ℝ) {k : Nat}
    (barriers : Fin k → ℝ) (S : Finset (Fin k)) :
    SpectralDecoherenceChannel.rate β (collectiveDecoherenceChannel barriers S) =
      EffectiveAction.decoherenceRate β (collectiveMeanBarrier barriers S) 1 := rfl

end PMAtoms
