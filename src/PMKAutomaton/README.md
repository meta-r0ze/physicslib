# PMKAutomaton

PMKAutomaton describes state and record transfer between E8 nodes. It is an E8
persistence automaton: a reversible cellular automaton on the E8 substrate.
See [the working premise](PREMISE.md) for the physical model and build layers.

Import `PMKAutomaton.Interface` for the handoff, record, cost, clock and
route and embedded symmetry theorems. Import `PMKAutomaton.Values` for the checked numbers and
their conditions. Use [the component inventory](COMPONENTS.md) and
`PMKAutomaton.Components` to locate the open contracts.

Run `./build.sh lean PMKAutomaton.Interface PMKAutomaton.Values PMKAutomaton.Components` for a
targeted check. The library build is `./build.sh PMKAutomaton`.

The [overview](OVERVIEW.md) lists the results. The [clock ledger](CLOCK.md)
gives the pulse constraints. The [premise ledger](PREMISES.md) lists the
remaining physical inputs.
