# PMTransport

PMTransport describes state and record transfer between E8 nodes.
See [the working premise](PREMISE.md) for the physical model and build layers.

Import `PMTransport.Interface` for the handoff, record, cost, clock and
route theorems. Import `PMTransport.Values` for the checked numbers and
their conditions.

Run `./build.sh lean PMTransport.Interface PMTransport.Values` for a
targeted check. The library build is `./build.sh PMTransport`.

The [overview](OVERVIEW.md) lists the results. The [clock ledger](CLOCK.md)
gives the pulse constraints. The [premise ledger](PREMISES.md) lists the
remaining physical inputs.

This README uses [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/about_STE.html).
