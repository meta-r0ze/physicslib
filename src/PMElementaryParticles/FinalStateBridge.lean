import PMElementaryParticles.CarrierSpecies

/-! **Comparison final-state charge ledger.**

This is a comparison ledger using SM species names.  The substrate-native
primary route is `SubstrateFinalStates`, built from the four base protocols.  A
channel records an initial species, a list of final species, and a proof that the
charge grading is conserved.
-/

noncomputable section
namespace PMElementaryParticles.FinalStateBridge

open PMElementaryParticles.CarrierBridge

/-- Total charge of a final-state list. -/
def chargeSum (l : List CarrierSpecies) : ℚ :=
  (l.map CarrierSpecies.charge).sum

/-- A final-state channel with conserved charge. -/
structure FinalStateChannel where
  name : String
  initial : CarrierSpecies
  final : List CarrierSpecies
  charge_conserved : initial.charge = chargeSum final

/-- Beta-minus base transition `d → u + e + ν`. -/
def betaMinus : FinalStateChannel where
  name := "d → u e ν"
  initial := .down
  final := [.up, .electron, .neutrino]
  charge_conserved := by
    norm_num [chargeSum, CarrierSpecies.charge]

/-- Neutrino species change with no charge transfer. -/
def neutrinoFinal : FinalStateChannel where
  name := "ν → ν"
  initial := .neutrino
  final := [.neutrino]
  charge_conserved := by
    norm_num [chargeSum, CarrierSpecies.charge]

/-- Every declared final-state channel conserves charge by construction. -/
theorem finalState_charge_conserved (c : FinalStateChannel) :
    c.initial.charge = chargeSum c.final := c.charge_conserved

/-- The base beta-minus ledger is neutral. -/
theorem betaMinus_charge :
    betaMinus.initial.charge = chargeSum betaMinus.final :=
  betaMinus.charge_conserved

end PMElementaryParticles.FinalStateBridge

/-! ## Richer particle final-state ledger -/

namespace PMElementaryParticles.FinalStateBridge.ParticleFinalStates

/-- Species used by the actual μ, τ, π, K channel inventory. -/
inductive DecaySpecies
  | electron | positron
  | muon | antimuon
  | tau | antitau
  | electronNeutrino | muonNeutrino | tauNeutrino
  | pionPlus | pionZero
  | kaonPlus
  deriving DecidableEq, Repr

/-- Electric charge in units of `e`. -/
def DecaySpecies.charge : DecaySpecies → ℚ
  | .electron => -1
  | .positron => 1
  | .muon => -1
  | .antimuon => 1
  | .tau => -1
  | .antitau => 1
  | .electronNeutrino => 0
  | .muonNeutrino => 0
  | .tauNeutrino => 0
  | .pionPlus => 1
  | .pionZero => 0
  | .kaonPlus => 1

def decayChargeSum (l : List DecaySpecies) : ℚ :=
  (l.map DecaySpecies.charge).sum

structure ParticleFinalStateChannel where
  name : String
  initial : DecaySpecies
  final : List DecaySpecies
  charge_conserved : initial.charge = decayChargeSum final

/-- `μ⁻ → e⁻ ν̄_e ν_μ`. -/
def muonDecay : ParticleFinalStateChannel where
  name := "e ν ν̄"
  initial := .muon
  final := [.electron, .electronNeutrino, .muonNeutrino]
  charge_conserved := by norm_num [decayChargeSum, DecaySpecies.charge]

/-- `τ⁻ → e⁻ ν̄_e ν_τ`. -/
def tauElectron : ParticleFinalStateChannel where
  name := "e ν ν̄"
  initial := .tau
  final := [.electron, .electronNeutrino, .tauNeutrino]
  charge_conserved := by norm_num [decayChargeSum, DecaySpecies.charge]

/-- `π⁺ → μ⁺ ν_μ`. -/
def pionMuon : ParticleFinalStateChannel where
  name := "μ⁺ ν"
  initial := .pionPlus
  final := [.antimuon, .muonNeutrino]
  charge_conserved := by norm_num [decayChargeSum, DecaySpecies.charge]

/-- `π⁺ → e⁺ ν_e`. -/
def pionElectron : ParticleFinalStateChannel where
  name := "e⁺ ν"
  initial := .pionPlus
  final := [.positron, .electronNeutrino]
  charge_conserved := by norm_num [decayChargeSum, DecaySpecies.charge]

/-- `K⁺ → μ⁺ ν_μ`. -/
def kaonMuon : ParticleFinalStateChannel where
  name := "μ⁺ ν"
  initial := .kaonPlus
  final := [.antimuon, .muonNeutrino]
  charge_conserved := by norm_num [decayChargeSum, DecaySpecies.charge]

/-- `K⁺ → π⁺ π⁰`. -/
def kaonPiPi0 : ParticleFinalStateChannel where
  name := "π⁺ π⁰"
  initial := .kaonPlus
  final := [.pionPlus, .pionZero]
  charge_conserved := by norm_num [decayChargeSum, DecaySpecies.charge]

/-- The particle final-state inventory. -/
def particleFinalStates : List ParticleFinalStateChannel :=
  [muonDecay, tauElectron, pionMuon, pionElectron, kaonMuon, kaonPiPi0]

end PMElementaryParticles.FinalStateBridge.ParticleFinalStates
