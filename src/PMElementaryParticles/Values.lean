import PMSubstrate.SpeciesFootprints
import PMElementaryParticles.SharedUnits
import PMElementaryParticles.PhysicalUnits
import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.QuarkMasses
import PMElementaryParticles.MuonLifetime
import PMElementaryParticles.MuonLifetimeCorrected
import PMElementaryParticles.TauE8
import PMElementaryParticles.MuonLifetimeHigherOrder
import PMElementaryParticles.TauLifetimeCorrected
import PMElementaryParticles.TauLifetime
import PMElementaryParticles.LeptonLifetime
import PMElementaryParticles.EPLabelGen

/-!
# Public EP exports

This module exports these names, and defines no new physical reading.

* SharedUnits: `me`, `hbarc`, `pi_b`, `a_b`, `g_b`, `fermiME_pos`, `fermiME_tight`.
* PhysicalUnits: `electronTime`, `electronTime_pos`, `electronTime_tight`,
  `muonLifetimeSeconds`, `muonLifetimeSeconds_tight`, `tauLifetimeSeconds`,
  `tauLifetimeSeconds_bounds`.
* MuonLifetime: `muonLifetime`, `muonLifetime_pos`.
* MuonLifetimeCorrected: `muonLifetimeCorrected`, `corrected_bounds`.
* MuonLifetimeHigherOrder: `lifetime`, `lifetime_bounds`.
* TauLifetimeCorrected: `tauLifeCorrected`, `tau_lifetime_corrected`.
* SpeciesFootprints.Lepton: `muon`, `tau`.
* SpeciesFootprints.Quark: `up`, `down`, `strange`, `charm`, `bottom`, `top`.
* LeptonMasses: `muon_value`, `tau_value`.
* QuarkMasses: `up_value`, `down_value`, `strange_value`, `charm_value`, `bottom_value`, `top_value`.
* TauLifetime: `tauLife`, `tau_lifetime_tree`.
* LeptonLifetime: `muonFiniteLifetime`, `muonFiniteLifetime_bounds`.
* TauE8: `tauLifetimeE8`, `tauLifetimeE8_bounds`.
* ProgramClasses: `classOf`, `visibleClasses`, `visibleClasses_card`, `visibleChannels`,
  `visible_channels_card`, `invisible_iff`.
* EPSpine: `Generation`, `generation_card`, `Program`, `programs_card`, `singlet_no_program`.
* EPLabelGen: `spine_generations`.

Tau lifetime APIs take their electronic branch, and where required muon time,
as arguments. Experimental instantiations live in e8p.
-/

namespace PMElementaryParticles.Values

export PMElementaryParticles.SharedUnits
  (me hbarc pi_b a_b g_b fermiME_pos fermiME_tight)
export PMElementaryParticles.PhysicalUnits
  (electronTime electronTime_pos electronTime_tight muonLifetimeSeconds muonLifetimeSeconds_tight
    tauLifetimeSeconds tauLifetimeSeconds_bounds)
export PMElementaryParticles.MuonLifetime (muonLifetime muonLifetime_pos)
export PMElementaryParticles.TauE8 (tauLifetimeE8)
export PMElementaryParticles.MuonLifetimeCorrected (muonLifetimeCorrected corrected_bounds)

export PMElementaryParticles.MuonLifetimeHigherOrder (lifetime lifetime_bounds)

export PMElementaryParticles.TauLifetimeCorrected (tauLifeCorrected tau_lifetime_corrected)

export PMSubstrate.SpeciesFootprints.Lepton (muon tau)
export PMSubstrate.SpeciesFootprints.Quark (up down strange charm bottom top)
export PMElementaryParticles.LeptonMasses (muon_value tau_value)
export PMElementaryParticles.QuarkMasses
  (up_value down_value strange_value charm_value bottom_value top_value)
export PMElementaryParticles.TauLifetime (tauLife tau_lifetime_tree)
export PMElementaryParticles (muonFiniteLifetime muonFiniteLifetime_bounds)
export PMElementaryParticles.TauE8 (tauLifetimeE8_bounds)

/-! ## Program spine -/

export PMElementaryParticles.ProgramClasses
  (classOf visibleClasses visibleClasses_card visibleChannels visible_channels_card invisible_iff)
export PMElementaryParticles.EPSpine
  (Generation generation_card Program programs_card singlet_no_program)
export PMElementaryParticles.EPLabelGen (spine_generations)

end PMElementaryParticles.Values
