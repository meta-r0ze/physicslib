# PMHadrons — the hadron level

Lean 4 proofs for the hadron level of the persistence ladder: quark composites, that is the
nucleons (proton, neutron) and the light mesons (π, K). It sits between
[`PMElementaryParticles`](../PMElementaryParticles/README.md) (the protocols and leptons it is
built from) and [`PMAtoms`](../PMAtoms/README.md) (nuclei and atoms built from nucleons).

```
PMElementaryParticles  →  PMHadrons  →  PMAtoms
 protocols, leptons        nucleons,      nuclei,
                           mesons         atoms
```

## Main results

- **Nucleons from the substrate.** `Nucleon` assembles the proton (`uud`, `Q = +1`) and neutron
  (`udd`, `Q = 0`) from three colour-axis protocols; three colour axes give baryon number `1`.
- **The six-pillar mass ledger.** `CompositeMasses` evaluates
  `m_p = Δ² − πD − 1/D + 5Z_TOL − Z_MAR/χ − α(D + 1/D)` (CODATA within `0.6σ`) and
  `m_n = Δ² − πD − 1/D + σ/2 + 3Z_TOL − Z_MAR` (within `0.1σ`); the nucleus ledger reuses
  their terms. The mesons carry the same pillars another way: `α⁻¹` is one substrate cell's
  six-pillar budget, with the same `Z_TOL` and `Z_MAR`, and each meson is a whole number of
  cell budgets plus a short residual (`MesonMasses`).
- **Stability and decays.** `Particle` proves `proton_stable` (baryon number forbids a lighter
  channel) and the allowed tree-level channels. `NeutronRate`, `PionWidth`, `KaonWidth` and
  `NeutralPionWidth` give the widths; `ParticleChannels` is the channel inventory.
- **The neutron lifetime from E8.** `NeutronPrediction` gives `877.2 s` (measured `878 s`) from
  the finite spectral channel on the minimal `3×3×3` cube (`MinimalCube`) with the `41/43`
  margin; `MesonFiniteChannels` gives the π and K finite channels.
- **Composite structure.** `CompositeStates`, `CompositeTransition`, `CompositePhaseSpace`,
  `CompositeBinding`, `HadronicMatrixElement` and `BoundStateOverlap` make the composite objects,
  and the missing bound-state input, explicit.

## Where to look

- **[OVERVIEW.md](OVERVIEW.md)**: what is proved, module by module, and the pillar audit.
- **[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)**: open work.

## Build and audit

```sh
./build.sh PMHadrons
```

`AuditDependencies` enforces the layering: `PMElementaryParticles` may not import `PMHadrons`,
and `PMHadrons` may not import `PMAtoms` or `PMCosmology`. Permitted axioms: `propext`,
`Classical.choice`, `Quot.sound`.
