import PMElementaryParticles.ProtocolInventory

/-! **Substrate-native final states.**

The primary final-state ledger uses the four base protocols of the 16-channel
inventory, not Standard-Model particle names.  A final state is admissible when
its base-protocol charge equals the initial charge.  SM names are comparison
labels applied afterwards.
-/

noncomputable section
namespace PMElementaryParticles.SubstrateFinalStates

open PMElementaryParticles.ProtocolInventory


/-- Total charge of a substrate final-state list. -/
def finalCharge (l : List BaseProtocol) : ℚ :=
  (l.map BaseProtocol.charge).sum

/-- Admissible substrate final state: charge is conserved. -/
def AdmissibleFinalState (initial : BaseProtocol) (final : List BaseProtocol) : Prop :=
  BaseProtocol.charge initial = finalCharge final

/-- The four base protocols available as substrate states. -/
def baseStates : List BaseProtocol :=
  [.electron, .up, .down, .neutrino]

/-- Substrate beta-minus final state: `down → up + electron + neutrino`. -/
theorem betaMinus_admissible :
    AdmissibleFinalState .down [.up, .electron, .neutrino] := by
  norm_num [AdmissibleFinalState, finalCharge, BaseProtocol.charge, PMElementaryParticles.ProtocolInventory.BaseProtocol.leptonAxis, PMElementaryParticles.ProtocolInventory.BaseProtocol.positiveSign, PMConstants.Hypercharge.electric, PMConstants.CarrierRepresentation.blAxis, PMConstants.CarrierRepresentation.t3Sign]

/-- A single base state is trivially admissible. -/
theorem single_admissible (b : BaseProtocol) :
    AdmissibleFinalState b [b] := by
  simp [AdmissibleFinalState, finalCharge, BaseProtocol.charge, PMElementaryParticles.ProtocolInventory.BaseProtocol.leptonAxis, PMElementaryParticles.ProtocolInventory.BaseProtocol.positiveSign, PMConstants.Hypercharge.electric, PMConstants.CarrierRepresentation.blAxis, PMConstants.CarrierRepresentation.t3Sign]

/-- The substrate inventory has exactly these four base states. -/
theorem baseStates_card : baseStates.length = 4 := rfl

end PMElementaryParticles.SubstrateFinalStates
