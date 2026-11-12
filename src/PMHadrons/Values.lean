import PMHadrons.CompositeMasses
import PMHadrons.MesonMasses
import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PMHadrons.KaonPionRatio
import PMHadrons.MesonFiniteChannels
import PMHadrons.NeutronPrediction
import PMHadrons.TollGovernor
import PMHadrons.DecayInstantiation

/-!
# PMHadrons canonical values

Single import for the hadron-level values that `PMAtoms` and `e8p` use, mirroring
`PMSubstrate.E8Values`, `PMConstants.Values`, `PMFlavor.Values` and
`PMElementaryParticles.Values`.

* Nucleons (`m_e` units): `proton`, `neutron` with `proton_value`, `neutron_value`;
  `protonRadius_value` (fm).
* Mesons: `pionPlus`, `pion0`, `kaon0`, `kaonPlus` with their `m_e` and MeV enclosures;
  `cellBudget` (one cell's six-pillar budget, `= α⁻¹`).
* Decay constants: `pionDecayConstantE8`, `kaonDecayConstantE8` (`v/1890`, `v/1593`) with their
  `m_e` and MeV bounds.
* Lifetimes: `neutronLifetimeUnifiedSeconds` (the one-template neutron, `R` from the running),
  `neutronLifetimeCorrectedSeconds`, `pionLifetimeCorrectedSeconds`,
  `neutralPionFiniteLifetimeSeconds` with bounds; `kaonPionWidthRatio` with bounds.
* Margins and emission: `neutronMarginFactor` (`= E8Margin.phaseMargin = 41/43`),
  `emissionWeight` (Toll), `governorPerSlot`.
-/

namespace PMHadrons.Values

export PMHadrons.CompositeMasses
  (proton neutron proton_value neutron_value protonRadius_value
    pion0 kaon0 kaonPlus pion0_value kaonPlus_value pion0_mev_value kaon0_mev_value
    kaonPlus_mev_value)
export PMHadrons.MesonMasses (pionPlus pionPlus_value pionPlus_mev_value cellBudget)
export PMHadrons.PionWidth
  (pionDecayConstantE8 pionDecayConstantE8_bounds pionDecayConstantMeV_bounds)
export PMHadrons.KaonWidth
  (kaonDecayConstantE8 kaonDecayConstantE8_bounds kaonDecayConstantMeV_bounds)
export PMHadrons.KaonPionRatio (kaonPionWidthRatio kaonPionWidthRatio_bounds)
export PMHadrons
  (neutronLifetimeCorrectedSeconds neutronLifetimeCorrectedSeconds_bounds neutronMarginFactor
    neutronMarginFactor_eq pionLifetimeCorrectedSeconds pionLifetimeCorrectedSeconds_bounds
    neutralPionFiniteLifetimeSeconds neutralPionFiniteLifetimeSeconds_bounds)
export PMHadrons.DecayInstantiation
  (neutronLifetimeUnifiedSeconds neutronLifetimeUnifiedSeconds_bounds)
export PMHadrons.TollGovernor (emissionWeight emissionWeight_pos governorPerSlot)

end PMHadrons.Values
