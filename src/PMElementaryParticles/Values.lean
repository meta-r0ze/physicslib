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
import PMElementaryParticles.GenerationMasses

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
* Lifetimes: `muonLifetimeSeconds` (tree level) with `muonLifetimeSeconds_tight`,
  `muonLifetimeCorrected` (derived phase factor, supplied one-loop QED) with `corrected_bounds`,
  `muonLifetimeFull` (the full Fermi-theory QED series of van Ritbergen–Stuart, supplied, at E8
  inputs) with `muonLifetimeFull_bounds` (`2.196974–2.196984 µs`),
  `tauLifetimeSeconds` with `tauLifetimeSeconds_bounds`; `tauLifetimeCorrectedFs` (the measured-`τ_μ`,
  supplied-`B_e` tau lifetime with the corrected partial-width ratio) with
  `tauLifetimeCorrectedFs_bounds` (`291.03–291.06` fs); `tauLife` with `tau_lifetime_tree`
  (tree level, fs); `muonFiniteLifetime`, `tauLifetimeE8` (natural units) with their bounds.
* Program spine: `Generation` with `generation_card` (3 glue cosets); `classOf` with
  `visibleClasses_card` (5 visible classes), `visible_channels_card` (15 channels) and
  `invisible_iff` (the total singlet is the one invisible class); `Program` with
  `programs_card` (15), `singlet_no_program`, and `spine_generations` (each generation and
  visible class has a program that meets all six pillars and keeps its generation and label on
  the ring).
* Generation masses (`GenerationMasses`): EP's generation is the upstream glue label
  (`label_eq_key`); the heavy generation, the one with the reference's label, is the glue key
  `(0,1)` (`heavy_iff`, `heavy_key`). No mass values yet (open upstream in `PMAction`).

This module only names results. Computation lives in its own modules (for example
`TransportCandidates`).
-/

namespace PMElementaryParticles.Values

export PMElementaryParticles.SharedUnits
  (me hbarc αe αinv fermiME pi_b a_b g_b fermiME_pos fermiME_tight)
export PMElementaryParticles.PhysicalUnits
  (electronTime electronTime_pos electronTime_tight muonLifetimeSeconds muonLifetimeSeconds_tight
    tauLifetimeSeconds tauLifetimeSeconds_bounds)
export PMElementaryParticles.MuonLifetime (muonLifetime muonLifetime_pos)
export PMElementaryParticles.TauE8 (tauLifetimeE8)
export PMElementaryParticles.MuonLifetimeCorrected (muonLifetimeCorrected corrected_bounds)

/-- The muon lifetime with the full Fermi-theory QED series. -/
noncomputable abbrev muonLifetimeFull : ℝ := PMElementaryParticles.MuonLifetimeHigherOrder.lifetime

theorem muonLifetimeFull_bounds :
    (2.196974e-6 : ℝ) < muonLifetimeFull ∧ muonLifetimeFull < (2.196984e-6 : ℝ) :=
  PMElementaryParticles.MuonLifetimeHigherOrder.lifetime_bounds

/-- The conditional tau lifetime (fs) with the corrected partial-width ratio. -/
noncomputable abbrev tauLifetimeCorrectedFs : ℝ := PMElementaryParticles.TauLifetimeCorrected.tauLifeCorrected

theorem tauLifetimeCorrectedFs_bounds :
    (291.03 : ℝ) < tauLifetimeCorrectedFs ∧ tauLifetimeCorrectedFs < 291.06 :=
  PMElementaryParticles.TauLifetimeCorrected.tau_lifetime_corrected

export PMElementaryParticles.LeptonMasses (muon tau muon_value tau_value)
export PMElementaryParticles.QuarkMasses
  (up down strange charm bottom top up_value down_value strange_value charm_value bottom_value
    top_value)
export PMElementaryParticles.TauLifetime (tauLife tau_lifetime_tree)
export PMElementaryParticles (muonFiniteLifetime muonFiniteLifetime_bounds)
export PMElementaryParticles.TauE8 (tauLifetimeE8_bounds)

/-! ## Program spine -/

export PMElementaryParticles.ProgramClasses
  (classOf visibleClasses visibleClasses_card visibleChannels visible_channels_card invisible_iff)
export PMElementaryParticles.EPSpine
  (Generation generation_card Program programs_card singlet_no_program)
export PMElementaryParticles.EPLabelGen (spine_generations)
export PMElementaryParticles.GenerationMasses (label_eq_key heavy_iff heavy_key)

end PMElementaryParticles.Values
