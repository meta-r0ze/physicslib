import PMHadrons.CompositeMasses
import PMHadrons.MesonMasses
import PMHadrons.PionWidth
import PMHadrons.KaonWidth
import PMHadrons.KaonPionRatio
import PMHadrons.MesonFiniteChannels
import PMHadrons.NeutronPrediction
import PMHadrons.TollGovernor
import PMHadrons.DecayInstantiation
import PMHadrons.NeutronContinuum
import PMHadrons.NeutralPionWidth
import PMSubstrate.E8Margin
import PMHadrons.ChargedCurrentRate

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
* Lifetimes: `neutronLifetimeContinuumCoulombSeconds` (the E8 neutron: continuum route with the
  Fermi factor's leading term, `923.37–923.39 s`), `neutronLifetimeContinuumSeconds` (no Coulomb),
  `neutronLifetimeUnifiedSeconds` (the `3³` spectral template, comparison),
  `pionMuLifetimeSeconds`, `kaonMuLifetimeSeconds` and `kaonPionRatioRadiative` (one charged-current
  normalization, `ChargedCurrentRate`), `neutralPionFiniteLifetimeSeconds`, with bounds;
  `pionLifetimeCorrectedSeconds` (the earlier `32/33` stage) and `kaonPionWidthRatio` (tree ratio).
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
  (pionDecayConstantE8 pionDecayConstantE8_bounds pionDecayConstantMeV_bounds pionLifetimeE8)
export PMHadrons.KaonWidth
  (kaonDecayConstantE8 kaonDecayConstantE8_bounds kaonDecayConstantMeV_bounds kaonLifetimeE8)
export PMHadrons.NeutralPionWidth (neutralPionLifetimeE8)
export PMSubstrate.E8Margin (pionCorrectedLifetime)
export PMHadrons.KaonPionRatio (kaonPionWidthRatio kaonPionWidthRatio_bounds)
export PMHadrons
  (neutronMarginFactor neutronMarginFactor_eq pionLifetimeCorrectedSeconds
    pionLifetimeCorrectedSeconds_bounds
    neutralPionFiniteLifetimeSeconds neutralPionFiniteLifetimeSeconds_bounds)
export PMHadrons.NeutronContinuum
  (neutronLifetimeContinuumSeconds neutronLifetimeContinuumSeconds_bounds
    neutronLifetimeContinuumCoulombSeconds neutronLifetimeContinuumCoulombSeconds_bounds)
export PMHadrons.DecayInstantiation
  (neutronLifetimeUnifiedSeconds neutronLifetimeUnifiedSeconds_bounds)
export PMHadrons.ChargedCurrentRate
  (pionMuLifetimeSeconds pionMuLifetimeSeconds_bounds kaonMuLifetimeSeconds
    kaonMuLifetimeSeconds_bounds kaonPionRatioRadiative kaonPionRatioRadiative_bounds)
export PMHadrons.TollGovernor (emissionWeight emissionWeight_pos governorPerSlot)

end PMHadrons.Values
