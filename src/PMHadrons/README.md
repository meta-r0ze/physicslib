# PMHadrons — composite systems on the E8 substrate

Lean 4 proofs for the **composite** level of the E8 substrate: elementary carriers persisting
together as a bound many-carrier configuration. It sits between
[`PMElementaryParticles`](../PMElementaryParticles/README.md) (the carriers) and
[`PMAtoms`](../PMAtoms/README.md) (the larger systems built from composites).

```
PMElementaryParticles  →  PMHadrons  →  PMAtoms
 carriers                 composite      nuclei,
 (protocols, leptons)      systems        atoms
```

## The frame

Elementary carriers combine into a configuration. A
configuration is a *new persistent system* when it occupies enough substrate cells — each cell
paying the six-pillar budget `α⁻¹` — and it can rearrange by emitting a carrier (a decay). So
the two E8 quantities at this level are:

* the configuration's **occupancy** → its mass (how much substrate the system holds);
* its **overlap with a single outgoing carrier** → its emission amplitude (how readily the
  system sheds a carrier).

The Standard-Model names (proton, neutron, pion, kaon) are **comparison labels**: they say which
E8 composite is being compared with which measured particle, so a derived value can be checked
against data. They are never inputs and never the mechanism. A column headed `0.6σ` is a
comparison, not a derivation.

## Main results

- **Composites assembled from carriers.** `Nucleon` builds the proton/neutron configurations
  from three colour-axis carrier slots — charge and baryon number are sums of substrate
  quantities, not assertions. `CompositeStates` builds meson/baryon cohorts (signed constituent
  lists).
- **Composite mass = occupancy cost.** `CompositeMasses` and `MesonMasses`: a composite costs a
  whole number of substrate cells (`n·α⁻¹ + residual`), or the `Δ²`-based nucleon account. The
  E8 value is derived; the measured mass is only the comparison. `Occupancy` formalizes the
  **minimum-room principle** (a persistent placement holds at least `n` cells; below `n` it
  rearranges) and derives the pion's lower bound `≥ χ` from colour neutrality. Both bases are
  **pillar counts**: a meson holds `χ + σ·ℓ` cells (Map base + Protocol direction count per
  line-tier carrier, `StrangeCarrier`) and the nucleon base `Δ²` is Margin's causal cone
  (`NucleonBase`).
- **Rearrangement and emission.** `Particle` (what persists, what rearranges),
  `ParticleChannels` (the channel inventory), `CompositeTransition`,
  `HadronicMatrixElement` / `BoundStateOverlap` (the missing emission overlap made explicit),
  and the widths `NeutronRate`, `PionWidth`, `KaonWidth`, `NeutralPionWidth`,
  `KaonSemileptonic`.
- **The neutron lifetime from a minimal E8 cube.** `NeutronPrediction` uses the minimal
  persistent cube `3×3×3` (`MinimalCube`) with the `41/43` margin — an E8 volume statement,
  not a spatial box.

## Where to look

- **[OVERVIEW.md](OVERVIEW.md)**: what is proved, module by module, the six-pillar occupancy
  account, and the E8 decay checks.
- **[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)**: open work — the composite's persistent
  configuration (occupancy) and its emission overlap.

## Build and audit

```sh
./build.sh PMHadrons
```

`AuditDependencies` enforces the layering: `PMElementaryParticles` may not import `PMHadrons`,
and `PMHadrons` may not import `PMAtoms` or `PMCosmology`. Permitted axioms: `propext`,
`Classical.choice`, `Quot.sound`.
