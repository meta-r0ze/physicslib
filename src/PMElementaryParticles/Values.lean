import PMElementaryParticles.SharedUnits
import PMElementaryParticles.PhysicalUnits
import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.QuarkMasses

/-!
# PMElementaryParticles canonical values

Single import for the units, couplings, masses and lifetimes that later libraries
(`PMHadrons`, `PMAtoms`, `e8p`) use, mirroring `PMSubstrate.E8Values`, `PMConstants.Values` and
`PMFlavor.Values`. Use these names instead of re-proving a bound locally.

* Units (CODATA 2022 inputs): `me` (MeV), `hbarc` (MeV·fm), `electronTime` (s) with
  `electronTime_tight`.
* Couplings: `αe`, `αinv` with `a_b`, `g_b`; `fermiME` (`G_F` in `m_e⁻²`) with `fermiME_pos` and
  `fermiME_tight` (`3.0456453–3.0456507 × 10⁻¹²`); `pi_b`.
* Masses (`m_e` units): `muon`, `tau` with `muon_value`, `tau_value`; quarks `up … top` with
  `up_value … top_value` (in MeV).
* Lifetimes: `muonLifetimeSeconds` with `muonLifetimeSeconds_tight`, `tauLifetimeSeconds` with
  `tauLifetimeSeconds_bounds`.
-/

namespace PMElementaryParticles.Values

export PMElementaryParticles.SharedUnits
  (me hbarc αe αinv fermiME pi_b a_b g_b fermiME_pos fermiME_tight)
export PMElementaryParticles.PhysicalUnits
  (electronTime electronTime_pos electronTime_tight muonLifetimeSeconds muonLifetimeSeconds_tight
    tauLifetimeSeconds tauLifetimeSeconds_bounds)
export PMElementaryParticles.LeptonMasses (muon tau muon_value tau_value)
export PMElementaryParticles.QuarkMasses
  (up down strange charm bottom top up_value down_value strange_value charm_value bottom_value
    top_value)

end PMElementaryParticles.Values
