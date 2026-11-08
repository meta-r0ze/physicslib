# PMSubstrate — Paper I substrate

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum I: The E8 Substrate and the
Fine-Structure Constant*.

- What is checked: [OVERVIEW.md](OVERVIEW.md) — main theorem, postulates, six terms, module map.
- What remains: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) — the missing physical implications.

Build: Lean 4.34.1, in the single Lake package of this repository, with the
vendored `classification/` package.

```sh
lake exe cache get
./build.sh PMSubstrate
```

`./build.sh PMSubstrate` builds the library. The whole-tree audits run with
`./build.sh audit` (strict axioms, readable/import checks, class-number audit).

- **E8Margin.** Substrate phase margin `(Δ−χ)/Δ = 41/43` and its application to channel weights.
