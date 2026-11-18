# PMTransport.Machine — native E8 operations

This folder contains the native carriers, registers, references, records, roots
and clock. It includes their reversible update and readout theorems.

- [Checked results](OVERVIEW.md)
- [Open work](../REVIEW-AND-NEXT.md)

The machine and the PMAction finite proofs share a build layer. Import
`PMTransport.Machine` to use its full interface. Import an individual module to
use a smaller part of it.

```sh
./build.sh lean PMTransport.Machine.CarrierEvents
./build.sh fast PMAction
```
