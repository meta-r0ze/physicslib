# PMCosmology — Paper VI cosmology library

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum VI*, the
**cosmological application** of the persistence framework. This is the most
draft-stage paper of the series: it proposes how a substrate **load** rescales
cosmological readouts, and checks the accompanying bookkeeping, capacity,
saturation, thermodynamic and primordial arguments. It builds on Papers I–V.

## Main results

- **Exact load.** `Scaling.exact_ratios`: the load is `L = 1491/1376`, the tilt
  `31/32`, the dark ratio `31/6` (all exact rationals).
- **Certified headline numbers.** `SubstrateLoad.revised_numerical_outputs` and
  `revised_numerical_bounds` give exact rationals and tight decimal enclosures for
  the paper's conditional rescalings `H_late = 67.4·L` and `S8_late = 0.832/L`.
- **Certified tensions.** `Tensions` certifies the propagated `0.5`/`0.013`
  uncertainties and the dark count `248/(48(1−2/43+α))`; `Scaling.disjoint_dark_count_check`
  proves the `31/6` vs `25/6` distinction. `Hypotheses.CosmoModel` bundles the
  load/response/continuity premises in one structure.
- **Readout + modes.** `Readout` defines the scale factor as the cube root of a
  comoving cell's volume and ties its density to PM-2 `Continuity` (matter `w=0`);
  `Modes` shows a source-free mode's amplitude/power is free, so the primordial
  spectrum needs initial data.
- **Persistence selection (reused).** `PersistenceSelection` states the cosmology-
  facing corollaries of `PM/lean`'s `PersistenceMechanics.Selection`
  (`higher_rate_vanishes`, `least_rate_takes_over`, `uniform_law_selected`):
  among an explicit option family, the least-cost/persistent member survives.
- **Finite capacity.** `InformationCapacity`: a saturated finite register cannot
  injectively encode a fresh independent label without extra capacity.
- **Saturation.** `Saturation`: residual-capacity speed, its zero at saturation,
  and exact weak-load remainder identities (local, not a metric).
- **Background / thermodynamics.** `Background`, `Thermodynamics`: conditional
  dilution/continuity and first-law identities (geometry, entropy law are inputs).
- **Primordial.** `Primordial`: the 32→16 relabeling obstruction, a retained
  binary record, two CP-to-baryon estimates with certified windows, and
  baryon-label conservation under iteration (CP alone gives no asymmetry).
- **Neutrino compatibility.** `NeutrinoCompatibility`: no common-scale tower fits
  the fixed oscillation windows; the factor-six proposal is excluded upstream.

## Where to look

- **[OVERVIEW.md](OVERVIEW.md)** — the module map, the certified numbers, and the
  **draft-status risks / possible bugs** (frozen inputs, CP discrepancy, dark-ratio
  ambiguity). **Start here.**
- **[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)** — the remaining work, split into
  Lean-checkable arithmetic and physical model inputs.

## Build and audit

Lean 4.34.1; keep Papers I–VI as sibling directories. Then:

```sh
source ~/.elan/env
./check.sh
```

`check.sh` builds `PMCosmology`, strictly audits declarations against `propext`,
`Classical.choice`, `Quot.sound`, and runs `../../calculations/check_load_consistency.py`
(exact-fraction arithmetic and LaTeX tag freshness).

## Verification

Run `./check.sh`. Permitted axioms `propext`, `Classical.choice`, `Quot.sound`.

## Draft status

Observational inputs (`67.4`, `0.832`, `(6.12 ± 0.04)×10⁻¹⁰`, …) are **frozen
comparison data**, not an updated survey. The load-response rules, background
laws and entropy/energy laws are **constitutive assumptions**. The headline
`H_late`/`S8` values are conditional rescalings, not a derivation of expansion
history or a likelihood result. See OVERVIEW for the specific tensions.
