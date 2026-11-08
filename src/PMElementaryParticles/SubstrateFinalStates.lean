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

/-- Charge of a base protocol, from the substrate inventory. -/
def baseCharge : BaseProtocol → ℚ
  | .electron => -1
  | .up => 2 / 3
  | .down => -1 / 3
  | .neutrino => 0

/-- Total charge of a substrate final-state list. -/
def finalCharge (l : List BaseProtocol) : ℚ :=
  (l.map baseCharge).sum

/-- Admissible substrate final state: charge is conserved. -/
def AdmissibleFinalState (initial : BaseProtocol) (final : List BaseProtocol) : Prop :=
  baseCharge initial = finalCharge final

/-- The four base protocols available as substrate states. -/
def baseStates : List BaseProtocol :=
  [.electron, .up, .down, .neutrino]

/-- Substrate beta-minus final state: `down → up + electron + neutrino`. -/
theorem betaMinus_admissible :
    AdmissibleFinalState .down [.up, .electron, .neutrino] := by
  norm_num [AdmissibleFinalState, finalCharge, baseCharge]

/-- A single base state is trivially admissible. -/
theorem single_admissible (b : BaseProtocol) :
    AdmissibleFinalState b [b] := by
  simp [AdmissibleFinalState, finalCharge, baseCharge]

/-- The substrate inventory has exactly these four base states. -/
theorem baseStates_card : baseStates.length = 4 := rfl

end PMElementaryParticles.SubstrateFinalStates
