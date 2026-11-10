# e8p — open work (todo)

`e8p` reports every value whose Lean proof exists as an exact-rational enclosure,
compares it with a frozen experimental reference, and can emit manuscript tags or an
audit. This file tracks coverage so the per-paper Python calculators can be retired
only when their values are Lean-backed here.

## Certified now (121 values)

- Paper 0: `delta`, `nu`, `sigma`, `chi`, `D` (substrate invariants); derived loads
  `l_intrinsic`, `l_embed`, `l_substrate`, `n`, `rm`; `nc`, `weinberg_gut`,
  `boundary_storage`.
- Paper 1: `alpha_inv`, `alpha`; the six α⁻¹ pillars `cap`, `map`, `protocol`,
  `governor`, `toll`, `margin` (the `Impedance` terms); and the readouts `c_light`,
  `von_klitzing`, `planck_charge_attenuation`, `planck_charge_ratio`, `planck_mass`.
- Paper 3: `eta` (overhead), `footprint`, `weak_fraction`, `lambda` (scalar),
  `scalar_toll`, `electron_yukawa`, `alpha_s`, `vev_over_me`, `electron_mass_input`,
  `vev`, `higgs_mass`, `fermi_constant`.
- Paper 3 extra: `alpha_G` (`PMConstants.GravityAccounting.channels_as_frame`),
  `beta_0` (`PMConstants.beta_positive_iff`), `w_ratio`
  (`PMConstants.WMassTest.ratio_bounds`), `gauge_hyper` / `gauge_colour`
  (`GaugeLedgers.hyper_value`, `ColourChannels.colour_ledger`), the uncorrected
  `w_mass_uncorrected` / `z_mass_uncorrected`, the couplings `g_weak` / `g_prime`,
  `electron_closure`, and `b_res`.
- Paper 4: `jarlskog` (`PMFlavor.CKM.pmJ_bounds`), `jarlskog_geo`
  (`pm3J_bounds`), `cabibbo` (`CKM.s12_bounds`); `wolf_lambda`, `wolf_A`,
  `wolf_rho`, `wolf_eta` (`PMFlavor.Wolfenstein.*_bounds`); `sin2_theta12`,
  `sin2_theta23`, `sin2_theta13` (`PMFlavor.PMNSIntervals.input_bounds`);
  `ckm_s13`, `ckm_s23`, `ckm_vcb`, `vud`, `vud_dressed` (`PMFlavor.CKM.*_bounds`,
  `PMFlavor.CabibboDressing.vudDressed_bounds`);
  `pmns_jarlskog` (`PMFlavor.PMNSIntervals.jarlskog_bounds`).
- Paper 5 / Atoms (`PMAtoms`): `rydberg_ev`, `bohr_radius`,
  `shell_capacity_n4`.
- Paper 5: `proton_ratio`, `neutron_ratio` (`PMHadrons.CompositeMasses.*_value`),
  `muon_ratio`, `tau_ratio` (`PMElementaryParticles.LeptonMasses.*_value`), `proton_radius`,
  `pion0_mev`, `kaon0_mev`, `kaon_plus_mev` (`CompositeMasses` pulls), and the six
  quark masses `up/down/strange/charm/bottom/top_mev` (`QuarkMasses.*_value`),
  `pion_plus_mev` (`PMHadrons.MesonMasses.pionPlus_mev_value`), the decay constants
  `f_pi_mev` / `f_k_mev` (`PMHadrons.PionWidth.pionDecayConstantMeV_bounds`,
  `PMHadrons.KaonWidth.kaonDecayConstantMeV_bounds`; FLAG 2024, `f_k_mev` is ~3.8σ low),
  `neutrino_floor_mass` (`FloorNeutrino.floor_bounds`), and `tau_lifetime_fs`
  (`PMElementaryParticles.TauLifetime.tau_lifetime_tree`).
- Paper 6: `baryon_pmJ`, `baryon_pm3J` (`PMCosmology.Primordial.baryon_windows`),
  `z_eq` (`PMCosmology.Background.z_eq_bounds`), `dark_raw` (`Scaling.exact_ratios`),
  `omega_ratio` (`PMCosmology.Tensions.omegaRatio_bounds`);
  `load` (`PMCosmology.Scaling.exact_ratios`), `hubble_late`,
  `clustering_late` (`PMCosmology.SubstrateLoad.revised_numerical_outputs`),
  `hubble_sigma`, `s8_sigma` (`PMCosmology.Tensions.*`), `omega_ratio`
  (`PMCosmology.Tensions.omegaRatio_bounds`).

## constants.txt parity — remaining values

Not yet in `e8p`, compared against `PM-1-Arch/calculations/constants.txt`:

- **Lean definition exists, needs numeric bounds**: the absolute W mass
  (`w_window` needs the measured `M_Z` as a supplied input).
- **No Lean enclosure yet**: `alpha_s` at the tau (three variants), `alpha⁻¹(m_Z)`,
  the electron-closure coefficient and mass ratio, the sigma/D Yukawa dressing,
  the uncorrected absolute W/Z masses, the interface factor `k`, the strong
  readout with `k`, the radiative correction `1−1/k`, the anti-screening term `X`,
  Higgs impedance, weak aperture, vacuum-energy scaling, and the physical
  wavelength `λ_min`.
- **Global audit/χ²**: now provided by `e8p --audit` (per-value σ and summary);
  a tiered audit can be added as `--audit --tier` if wanted.

## Decay coverage

Catalogued decay quantities now include `tau_lifetime_fs`, the finite-channel
muon and neutron lifetimes (`muon_lifetime_finite`, `muon_lifetime_s`,
`neutron_spectral_fraction`, `neutron_lifetime_e8`, `neutron_lifetime_s`), the
natural-unit E8 tau lifetime (`tau_lifetime_e8_natural`), and the meson finite
channels: `pion_finite_width`, `pion_finite_lifetime`, `kaon_finite_width`,
`kaon_finite_lifetime`, `neutral_pion_finite_width`, and
`neutral_pion_finite_lifetime`, plus their physical-unit forms
`pion_finite_lifetime_s`, `kaon_finite_lifetime_s`, and
`neutral_pion_finite_lifetime_s`. The intervals are still broad; they are
certified, but not yet precise enough for meaningful σ comparisons.

The meson channels use the minimal `3×3×3` cube and the parent mass as cutoff.
Since all three cutoffs exceed the universal eigenvalue bound `12`, every mode
is open and the finite spectral fraction is exactly one; the finite width is
therefore the continuum width. The neutron remains the special case because its
cutoff lies in the first spectral gap.

Known comparison caveats (uncorrected W/Z, undressed Vud, documented mass
tensions) are printed by `--audit` and included as `caveat` fields in JSON.

## Not catalog values

Several "easy" items turned out not to be numeric values, so they stay out of `e8p`:
`LinkMass` / `ChainCouplings` are symbolic mass-term identities, `MassiveWidth`
widths are parametric, `ScalarAccounting.payload_*` is parametric in `G_F`, and
`NeutrinoCompatibility` is a negative result. `WMassTest` contributes the certified
`w_ratio`; its absolute mass still needs the measured `M_Z` as a supplied input.

## Comparison leaves (measured pulls out of `src`)

The measured comparisons were extracted from the `src` derivation modules into
`tools/e8p/E8PConstants/` leaves, leaving only E8-only enclosures in `src`:

- `LeptonMassPulls` — `muon_tension`, `tau_tension`, `pionPlus_mass`, `kaon_inversion`,
  `pion_splitting` (from `PMElementaryParticles.LeptonMasses`).
- `QuarkMassPulls` — `pulls` (from `PMElementaryParticles.QuarkMasses`).
- `WeakMassPulls` — `w_window`, `pull_world/cms/cdf/sm` (from `PMConstants.WMassTest`).
- `TauLifetimePulls` — `tau_lifetime_pull` (from `PMElementaryParticles.TauLifetime`).
- `ScalarAccounting.higgs_pull` (from `PMConstants.ScalarSector`).
- `ReadoutPulls` — `raw_w_window`, `raw_excluded`, `ledgers_are_effective`,
  `normalization_decided`, `w_mass`, `intensive_preferred`, `quark_w_window`,
  `quark_reference_excluded`, `reference_selected_wmass`.

The catalog proofs now cite the E8-only enclosures (`up_value`…`top_value`,
`pionPlus_mev_value`) in `src`; the comparison leaves do not feed any derivation.

## Harder: Python value exists, no Lean enclosure yet

These need new interval proofs (and sometimes a supplied input) before they can
enter the catalog:

- Paper 1: running `alpha(m_Z)` (needs the measured hadronic `Δα` input), and
  `alpha_s` at the tau (needs the Paper V flavour thresholds).
- Paper 3: the scalar VEV step formulas.
- Paper 4: the remaining CKM matrix entries `|V_td|`, `|V_ts|`, and the CP
  invariants `ε_K`, `sin2β`.
- Paper 6: the neutrino mass sum (only the one-sided `FloorNeutrino.tower_sum`
  bound exists).

## Experimental comparison backlog

Common measurements worth adding as extra references (the model values already
exist unless noted):

- **Multiple references per value**: `alpha_inv` from CODATA, Morel 2020,
  Parker 2018 and Fan 2023 (constants.txt already records all four), and
  `H0`/`S8` from Planck, SH0ES, DES and KiDS. This needs `ExpRef` to become a
  list; the reporter already computes σ per reference.
- **On-shell vs MS-bar**: `sin2_theta_W(MS-bar) = 0.23122`, replacing the
  current on-shell `weak_fraction = 0.222905`.
- **CKM/PMNS**: `delta_CP` (NuFIT), the two neutrino mass splittings
  `Δm²21`, `|Δm²31|`, and `|V_td|`, `|V_ts|`, `ε_K`, `sin2β` (`|V_ud|` is now
  catalogued). The PMNS δ angle is currently only bounded as `(π, 2π)`.
- **Cosmology**: `Omega_b h²`, `Omega_c h²`, `Omega_Lambda`, `n_s`, `A_s`,
  `N_eff`, `Y_p`, `D/H`, and recombination `z_*`. These are not missing proofs:
  the papers define no Lean densities/amplitudes for them, so adding them would
  mean new model postulates, not a catalog row.
- **Precision/QCD**: `g-2` (muon anomaly), neutron lifetime, `Λ_QCD`,
  `f_pi`, W/Z widths; none has a Lean enclosure yet.

## Scripts to retire, once fully covered

- `PM-1-Arch/calculations/constants.py`, `particles.py`
- `PM-3-Nested/calculations/e8_impedance_calculator.py`, `e8_capacity_conservation_gravity.py`
- `PM-4-Dynamics/calculations/flavor_geometry.py`
- `PM-6-Cosmo/calculations/cosmology.py`

Keep `check_load_consistency.py` as the independent exact-rational tag-freshness check
until the LaTeX pipeline is pointed at `e8p --latex`.

## Tool backlog

- Emit `--audit` tiers (bosonic / spectrum / combined).
- `--line-table` reports the line/ring mass diagnostic (E8 weights, RMS 0.0096 u
  vs 0.0168 u for the A-link budget); the Coulomb/valley term is not included.
- `--nuclear` reports the proved typed counts and He-4 closure; the periodic
  table still uses the mean `A`-link budget, not the graph weights.
- `--periodic-table` is implemented for Z=1..20 (shell occupations + E8 lattice
  weight vs standard weight). Extend it once the E8 persistence/rate ledger can
  mark persistent nuclides.
- Add `--particle <spec>`: accept `6 7` aka carbon 13 v.s. the more stable carbon 12, print `Z/N/A`, configuration, shell counts, E8 lattice mass, tabulated isotopic mass and half-life/decay. This is a lookup/display feature over frozen isotope data, not a new model value.
- Add a `--cite` mode.
- Point the papers' `\CatchFileBetweenTags` at `e8p --latex` output.
- Rename the directory to the final package name if `e8p` is kept as the binary.
