# PMAction/Machine — the native E8 finite machine

The subset of Paper II that builds the **native E8 finite machine**: the carrier
labels, registers, references, records, roots, readout, clock and parity/Weyl
structures, and their reversible protocols.

- What is checked: [OVERVIEW.md](OVERVIEW.md).
- What remains / organization backlog: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md).

## Import boundary

The machine's **only external base is `PMSubstrate`** (channels, channel
symmetry, lattices, `NetCost`, `PersistenceEvents`, `E8Values`) plus Mathlib — no
`PersistenceMechanics`, no other paper. It sits below the PMAction action/gauge
core: the machine does not import the action core, while a few core modules
(`MainTheorem`, `CommonResponse`) import the machine.

The machine still has outgoing imports into ~36 non-machine PMAction modules (8 of
them mutual). Reducing those to make the folder self-contained is the open
organization item; see [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md).

## Build

```sh
./build.sh lean PMAction.Machine.CarrierEvents   # one module, no OLean
./build.sh fast PMAction                          # OLeans for the whole library
```
