# PMAtoms — open work

**Open.** The bulk: with both isospin terms present the stable-line masses are `≈ 110 m_e`
heavy on average, because `certifiedMass`'s bulk terms (and the alpha-cluster binding) already
carry the average symmetry cost along the line. A full-chart ledger needs the bulk re-derived
with the isospin terms present; the occupancy ledger's symmetric filling energy has no E8 link
potential to pair with (`IsospinLedger` docstring). Until then the valley (which `(Z, N)` are
stable, `NuclearRegime`/`PersistenceSelection`) is a comparison, not a result.


- Derive the fragment overlap for α/fission hindrance using the composite configuration required by `PMHadrons.Emission`. Compare the odd-A α cases in `ALPHA-TESTS.md`.
- Derive a low-Z-anchored finite-size charge differential from the lattice Coulomb calculation.
- Derive screening and the electron fill order used by the atomic configurations.
- Keep continuum comparisons until each E8 replacement has a numerical counterpart. Mark candidate modules experimental, align the folder maps and keep measured residuals in `RESIDUALS.md`.
