import PMAtoms.SpectralWaveBridge
import PMAtoms.LeptonLifetime
import PMAtoms.NeutronPrediction
import PMAtoms.MesonFiniteChannels
import Mathlib.Tactic

/-! **Model-input phase channels.**

The `phaseCost` used here is the proposed spectral-weight mean eigenvalue from
`SpectralWaveBridge`.  It is a model choice, not an E8-derived number and not
the population fraction.  These instances keep the population lifetime and the
decoherence rate as separate objects.
-/

noncomputable section
namespace PMAtoms

open PersistenceMechanics
open PersistenceMechanics.EffectiveAction

/-- Muon finite-spectrum decoherence channel. -/
def muonDecoherenceChannel : SpectralDecoherenceChannel :=
  spectralDecoherenceChannel 3
    (betaOpenModes 3 PMElementaryParticles.LeptonMasses.muon)

/-- Neutron finite-spectrum decoherence channel. -/
def neutronDecoherenceChannel : SpectralDecoherenceChannel :=
  spectralDecoherenceChannel neutronCube
    (betaOpenModes neutronCube neutronCutoff)

/-- Charged-pion finite-spectrum decoherence channel. -/
def pionDecoherenceChannel : SpectralDecoherenceChannel :=
  spectralDecoherenceChannel mesonFiniteCube
    (betaOpenModes mesonFiniteCube pionFiniteCutoff)

/-- Charged-kaon finite-spectrum decoherence channel. -/
def kaonDecoherenceChannel : SpectralDecoherenceChannel :=
  spectralDecoherenceChannel mesonFiniteCube
    (betaOpenModes mesonFiniteCube kaonFiniteCutoff)

/-- Neutral-pion finite-spectrum decoherence channel. -/
def neutralPionDecoherenceChannel : SpectralDecoherenceChannel :=
  spectralDecoherenceChannel mesonFiniteCube
    (betaOpenModes mesonFiniteCube neutralPionFiniteCutoff)

theorem muonDecoherenceChannel_rate (β : ℝ) :
    SpectralDecoherenceChannel.rate β muonDecoherenceChannel =
      EffectiveAction.decoherenceRate β
        (spectralMeanCost 3 (betaOpenModes 3 PMElementaryParticles.LeptonMasses.muon)) 1 :=
  spectralDecoherenceChannel_rate β 3 _

theorem neutronDecoherenceChannel_rate (β : ℝ) :
    SpectralDecoherenceChannel.rate β neutronDecoherenceChannel =
      EffectiveAction.decoherenceRate β
        (spectralMeanCost neutronCube (betaOpenModes neutronCube neutronCutoff)) 1 :=
  spectralDecoherenceChannel_rate β neutronCube _

theorem pionDecoherenceChannel_rate (β : ℝ) :
    SpectralDecoherenceChannel.rate β pionDecoherenceChannel =
      EffectiveAction.decoherenceRate β
        (spectralMeanCost mesonFiniteCube
          (betaOpenModes mesonFiniteCube pionFiniteCutoff)) 1 :=
  spectralDecoherenceChannel_rate β mesonFiniteCube _

theorem kaonDecoherenceChannel_rate (β : ℝ) :
    SpectralDecoherenceChannel.rate β kaonDecoherenceChannel =
      EffectiveAction.decoherenceRate β
        (spectralMeanCost mesonFiniteCube
          (betaOpenModes mesonFiniteCube kaonFiniteCutoff)) 1 :=
  spectralDecoherenceChannel_rate β mesonFiniteCube _

theorem neutralPionDecoherenceChannel_rate (β : ℝ) :
    SpectralDecoherenceChannel.rate β neutralPionDecoherenceChannel =
      EffectiveAction.decoherenceRate β
        (spectralMeanCost mesonFiniteCube
          (betaOpenModes mesonFiniteCube neutralPionFiniteCutoff)) 1 :=
  spectralDecoherenceChannel_rate β mesonFiniteCube _

end PMAtoms
