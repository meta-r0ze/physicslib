# e8p — open work

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

- **Precision/QCD**: `g-2` (muon anomaly), `Λ_QCD`, W/Z widths; none has a Lean enclosure yet.

## Scripts to retire, once fully covered

- `PM-1-Arch/calculations/constants.py`, `particles.py`
- `PM-3-Nested/calculations/e8_impedance_calculator.py`, `e8_capacity_conservation_gravity.py`
- `PM-4-Dynamics/calculations/flavor_geometry.py`
- `PM-6-Cosmo/calculations/cosmology.py`

Keep `check_load_consistency.py` as the independent exact-rational tag-freshness check
until the LaTeX pipeline is pointed at `e8p --latex`.


## Tool backlog

- Emit `--audit` tiers (bosonic / spectrum / combined).

- `--nuclear` still prints the He-4 closure gap, the mirror link difference and the static
  charge energies as text citing their theorems; print them from `src/` values if a computable
  form is added there.
- The hydrogenic cloud column (`cloudSum`) is a rational mirror of
  `PMAtoms.ElectronCloud.bindingEV`; move a `ℚ` form into `src/` to drop the mirror.
- Add `--particle <spec>`: accept `6 7` aka carbon 13 v.s. the more stable carbon 12, print `Z/N/A`, configuration, shell counts, `2S+1`, E8 nuclear mass (`certifiedMass`), tabulated isotopic mass and half-life/decay. This is a lookup/display feature over frozen isotope data, not a new model value.
- **Kaon lifetime.** `kaon_finite_lifetime_s` (1.98–2.12 ×10⁻⁸ s) is still the broad enclosure and
  carries no reference. The E8 value is `≈ 2.015×10⁻⁸` s against the K_μ2 partial lifetime
  `τ_K/BR(μν) = 1.948×10⁻⁸` s (+3.5%): `f_K` (−0.7%) accounts for +1.5%; the pion's `32/33`
  margin is not applied to the kaon, and the SM radiative correction is about −2%. Tighten it
  (needs tight `kaonPlus` and `|V_us|` bounds) before adding the reference.
- **Electron-mass inputs.** `ElectroweakBounds.electronGeV`, `FloorNeutrino.meEV` and
  `StrongRunning.mZ` use `0.51099895` (CODATA truncated by `1.35×10⁻⁹`); `SharedUnits.me` and
  `Hydrogen.electronMassEV` use the full `0.51099895069`. Negligible at those rows' precision;
  unify on `SharedUnits.me` when their proofs are next touched. `SharedUnits.hbarc = 197.3269804`
  is likewise truncated (`2×10⁻¹⁰`).

- `E8TickUnit` and `AlphaClockComparison` (now `E8PConstants/PMAtoms/`) are model definitions no row uses; move them to `src/`
  or drop them from `PMAtoms/OVERVIEW.md`. `ledgerScatterME = 4.8` is typed in; compute it from
  the isotope table.
- **Candidate scalar rows from `src/`**: `K_ℓ3` at leading order (`PMHadrons.KaonSemileptonic`),
  the shell spacing coefficient `χ·m_p/Δ`, the O-17 spin–orbit splitting. Each needs a theorem
  with numeric bounds.
- **Shell adjacency in Lean.** `--shells` sorts `nilssonE8CostQ`; a `decide` theorem that the
  sorted ladder is the one printed would move the adjacency from the tool into `src/`.
- Add a `--cite` mode.
- Point the papers' `\CatchFileBetweenTags` at `e8p --latex` output.
- Rename the directory to the final package name if `e8p` is kept as the binary.

Tighten the broad natural-unit muon, tau and neutron lifetime rows and finite meson bounds when their source enclosures improve.
