# PMChemistry — overview

Which electron configurations sit on the substrate, and how they compare to
chemistry. Entry points are theorem names.

## Derived (E8 / combinatorics)

- **Shell capacities.** `PMAtoms.Shells.orbitalCapacity = 2(2ℓ+1)` and
  `shellCapacity n = 2n²`: the `2ℓ+1` magnetic states times the spin-2 rank of the
  PM-2 chiral projector (`spinStates_eq_trace`).
- **The Aufbau order is the Madelung order.** `Aufbau.madelungKey` (`(n+ℓ)·8+n`),
  `aufbau_sorted` (keys strictly increasing), `aufbau_nodup`, and the subshell
  capacities `subshellCapacity_eq = 4ℓ+2`.
- **Configuration filling.** `Aufbau.fill`, `Aufbau.configuration`.

## Model inputs / open

- The *order itself*: the hydrogenic energy `−R∞/n²` carries no `ℓ`-dependence, so
  the Madelung/Aufbau order is a supplied model input here (see
  [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)). The capacities are derived; the order
  is not.
- Screening/exchange, valence geometry and bonding are unmodeled.

## Comparison

Chemistry-level observables (ionization energies, valence, periodic-table groups)
are compared outside the axiom-checked tree, like the other modules' measured
references. The `e8p` periodic-table readout lives in `tools/e8p`.
