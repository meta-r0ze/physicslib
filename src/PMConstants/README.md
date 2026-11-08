# PMConstants — Paper III constants and selection constraints

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum III: Nested Persistence*
— constants, sectors, running and gauge factors.

- What is checked: [OVERVIEW.md](OVERVIEW.md) — module map and results.
- What remains: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) — constant-by-constant open
  physical dependencies.

Build: Lean 4.34.1, in the single Lake package of this repository, with
`PersistenceMechanics`, `PMSubstrate` and `PMAction`.

```sh
source ~/.elan/env
./build.sh PMConstants
```

The dependency direction is Paper I → Paper II → Paper III. Run
`./build.sh PMAction` before this one. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted;
no `sorry`, custom axioms or `native_decide`.
