import PMElementaryParticles.ParticleChannels
import PMElementaryParticles.FinalStateBridge

/-! **Link the particle-channel inventory to final-state species.**

The rate inventory in `ParticleChannels` and the charge ledger in
`FinalStateBridge` are connected by matching channel names.  This is a name-level
bridge; the physical matrix elements remain open.
-/

noncomputable section
namespace PMElementaryParticles.ChannelFinalStateLink

open PMElementaryParticles.ParticleChannels
open PMElementaryParticles.FinalStateBridge.ParticleFinalStates

theorem muon_names :
    (muonChannels.map (fun c => c.name)) = [muonDecay.name] := rfl

theorem tau_first_name :
    (tauChannels.map (fun c => c.name)).head? = some tauElectron.name := rfl

theorem pion_names :
    (pionChannels.map (fun c => c.name)) = [pionMuon.name, pionElectron.name] := rfl

theorem kaon_prefix :
    (kaonChannels.map (fun c => c.name)).take 2 = [kaonMuon.name, kaonPiPi0.name] := rfl

/-- Every final-state channel in the inventory has conserved charge. -/
theorem finalStates_charge_conserved
    (c : ParticleFinalStateChannel)
    (_hc : c ∈ (particleFinalStates : List ParticleFinalStateChannel)) :
    DecaySpecies.charge
        (ParticleFinalStateChannel.initial c) =
      decayChargeSum
        (ParticleFinalStateChannel.final c) :=
  ParticleFinalStateChannel.charge_conserved c

end PMElementaryParticles.ChannelFinalStateLink
