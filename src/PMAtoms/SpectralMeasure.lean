import PMElementaryParticles.BetaLattice
import PMHadrons.NeutronPrediction
import PMElementaryParticles.LeptonMasses
import PersistenceMechanics.ChannelMeasure
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Beta spectral channel measure

The finite beta spectral weights as a `ChannelMeasure`.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

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

/-- Probability of the muon-cutoff selected modes in the minimal cube. -/
noncomputable def muonSelectedProbability : ℝ :=
  betaSelectedProbability 3 PMElementaryParticles.LeptonMasses.muon

theorem muonSelectedProbability_nonneg : 0 ≤ muonSelectedProbability :=
  betaSelectedProbability_nonneg 3 _

end PMAtoms
