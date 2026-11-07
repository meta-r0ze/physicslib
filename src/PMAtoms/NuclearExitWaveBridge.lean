import PMAtoms.NuclearDecay
import PMAtoms.CollectiveWaveBridge
import Mathlib.Tactic

/-! **Structural bridge for the standard nuclear exit table.**

The four exits β⁻, β⁺, α, fission are represented as a `Fin 4` barrier vector.
Their finite collective rate is the normalized barrier-weight population rate;
the phase-loss channel uses the barrier-weight mean as an explicit model input.
No numerical lifetime is asserted here.
-/

noncomputable section
namespace PMAtoms

open PersistenceMechanics
open PersistenceMechanics.EffectiveAction

/-- Barrier vector for the standard β⁻/β⁺/α/fission exit table. -/
def nuclearExitBarrier (p f1 f2 : Nuclide) : Fin 4 → ℝ :=
  ![ (betaMinusExit p).barrier
   , (betaPlusExit p).barrier
   , (alphaExit p).barrier
   , (fissionExit p f1 f2).barrier ]

/-- Finite collective fraction of the standard exit table. -/
def nuclearExitFraction (p f1 f2 : Nuclide) : ℝ :=
  collectiveFraction (nuclearExitBarrier p f1 f2) Finset.univ

/-- Generic decay channel for the standard exit table. -/
def nuclearExitDecayChannel (c0 : ℝ) (p f1 f2 : Nuclide) : Decay.DecayChannel :=
  collectiveDecayChannel c0 (nuclearExitBarrier p f1 f2) Finset.univ

theorem nuclearExitDecayChannel_rate (β c0 : ℝ) (p f1 f2 : Nuclide) :
    Decay.rate β (nuclearExitDecayChannel c0 p f1 f2) =
      collectiveFiniteRate β c0 (nuclearExitBarrier p f1 f2) Finset.univ :=
  collectiveDecayChannel_rate β c0 _ _

theorem nuclearExitDecayChannel_lifetime (β c0 : ℝ) (p f1 f2 : Nuclide) :
    Decay.lifetime β (nuclearExitDecayChannel c0 p f1 f2) =
      collectiveLifetime β c0 (nuclearExitBarrier p f1 f2) Finset.univ :=
  collectiveDecayChannel_lifetime β c0 _ _

/-- Phase-loss channel for the standard exit table. -/
def nuclearExitDecoherenceChannel (p f1 f2 : Nuclide) : SpectralDecoherenceChannel :=
  collectiveDecoherenceChannel (nuclearExitBarrier p f1 f2) Finset.univ

theorem nuclearExitDecoherenceChannel_rate (β : ℝ) (p f1 f2 : Nuclide) :
    SpectralDecoherenceChannel.rate β (nuclearExitDecoherenceChannel p f1 f2) =
      EffectiveAction.decoherenceRate β
        (collectiveMeanBarrier (nuclearExitBarrier p f1 f2) Finset.univ) 1 :=
  collectiveDecoherenceChannel_rate β _ _

end PMAtoms
