# PMChemistry — the chemistry pillar (scaffold)

A scaffold module for chemistry on the E8 / Persistence Mechanics substrate: the
electron shell structure and the Aufbau order, built on `PMAtoms.Shells` and
`PMAtoms.ElectronCloud`. It exists so the chemistry comparison has a home separate
from the nuclear mass ledger.

- What is checked: [OVERVIEW.md](OVERVIEW.md).
- What remains: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md).

## Import boundary

Depends on `PMAtoms` only (shell capacities, electron cloud, hydrogenic energy).
No later paper. A library in its own right so the chemistry logic grows without
overloading `PMAtoms`.

## Build

```sh
./build.sh PMChemistry
./build.sh lean PMChemistry.Aufbau    # one module, no OLean
```
