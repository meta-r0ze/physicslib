# PMConstants — Paper III constants and selection constraints

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum III: Nested Persistence*
— constants, sectors, running and gauge factors.

Use [Values](Values.lean) for the public constants. The carrier axis and sign determine the
electric and hypercharge readouts. The substrate footprints supply the strong-running
thresholds. Measured inputs and the comparison proofs are in
[e8p](../../tools/e8p/README.md).

- What is checked: [OVERVIEW.md](OVERVIEW.md) — module map and results.
- What remains: [TODO.md](TODO.md) — constant-by-constant open
  physical dependencies.

Build: Lean 4.34.1, in the single Lake package of this repository, with
`PersistenceMechanics`, `PMSubstrate` and `PMAction`.

```sh
source ~/.elan/env
./build.sh PMConstants
```

The general nested rules are owned by `PersistenceMechanics.CapacityPartitioning`,
`ReversibleEncoding` and `ImpedanceMatching`. `General.ReferenceCapacity` keeps
its distinct finite-frame and clock applications. `Interface` keeps the concrete
quotient/remainder instance. The substrate-free accounting, hierarchy, service, transfer-persistence and work-selection
modules also live upstream. No compatibility copies of the generic rules remain.

The dependency direction is Paper I → Paper II → Paper III. Run
`./build.sh PMAction` before this one. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted;
no `sorry`, custom axioms or `native_decide`.
