# PMTransport

PMTransport describes state and record transfer between E8 nodes.
See [the working premise](PREMISE.md) for the physical model and build layers.

Import `PMTransport.Interface` for the handoff, record, cost, clock and
route and embedded symmetry theorems. Import `PMTransport.Values` for the checked numbers and
their conditions. Use [the component inventory](COMPONENTS.md) and
`PMTransport.Components` to locate the open contracts.

Run `./build.sh lean PMTransport.Interface PMTransport.Values PMTransport.Components` for a
targeted check. The library build is `./build.sh PMTransport`.

The [overview](OVERVIEW.md) lists the results. The [clock ledger](CLOCK.md)
gives the pulse constraints. The [premise ledger](PREMISES.md) lists the
remaining physical inputs.
