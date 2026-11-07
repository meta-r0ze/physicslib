import PMAtoms.BetaLattice
import PMAtoms.NeutronPrediction
import PersistenceMechanics.ChannelMeasure
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Beta spectral channel measure

The finite beta spectral weights as a `ChannelMeasure`.
-/

noncomputable section
namespace PMAtoms

open PersistenceMechanics.ChannelCounting

/-- Beta spectral measure on the `n×n×n` mode set. -/
def betaChannelMeasure (n : Nat) : ChannelMeasure (Fin n × (Fin n × Fin n)) :=
  { weight := fun p =>
      betaSpectralWeight n (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) }

/-- Probability of the cutoff-selected beta modes. -/
noncomputable def betaSelectedProbability (n : Nat) (E : ℝ) : ℝ :=
  subsetProbability (betaChannelMeasure n) (betaOpenModes n E)

theorem betaSelectedProbability_nonneg (n : Nat) (E : ℝ) :
    0 ≤ betaSelectedProbability n E := by
  unfold betaSelectedProbability
  apply subsetProbability_nonneg
  intro p
  exact le_of_lt (betaSpectralWeight_pos n _ _ _)

/-- Probability of the neutron-endpoint selected beta modes. -/
noncomputable def neutronSelectedProbability : ℝ :=
  betaSelectedProbability neutronCube neutronCutoffExact

theorem neutronSelectedProbability_nonneg : 0 ≤ neutronSelectedProbability :=
  betaSelectedProbability_nonneg neutronCube neutronCutoffExact

end PMAtoms
