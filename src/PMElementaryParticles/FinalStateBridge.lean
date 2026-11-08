import PMElementaryParticles.CarrierSpecies

/-! **Final-state charge ledger.**

This is the first B1 bridge: a decay channel records an initial species, a list
of final species, and a proof that the charge grading is conserved.  It does not
yet supply the physical matrix element or the full particle inventory.
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
