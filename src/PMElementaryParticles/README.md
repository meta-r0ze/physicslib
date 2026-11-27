# PMElementaryParticles

EP classifies programs on the E8 node machine and checks conditional decay widths.
It builds on PMSubstrate, PMAction, PMConstants and PMKAutomaton. PMFlavor follows EP.

The [overview](OVERVIEW.md) maps programs, pillars, charge, occupancy cost and decay.
The [generation-orbit table](OVERVIEW.md#generation-orbits) separates the full
clock-root groups from their label-respecting subgroups.
The [isolated-persistence section](OVERVIEW.md#persistence-of-an-isolated-excitation)
records the missing occupied-background renewal rule for decay. The
[program-dimension section](OVERVIEW.md#program-dimension) separates held events,
registration bounds and the geometric ring-embedding obstruction.
The [open list](TODO.md) records the missing physical identifications.
The [scope ledger](../../SCOPE.md#named-premises) records shared premises.

`PMElementaryParticles.Values` exports the public masses, unit conversions and lifetime APIs.
Measured tau inputs enter only in e8p. The physical mass reading is upstream
`PMSubstrate.OccupancyCost.cost`; species counts and residuals remain supplied.

Check a module with `./build.sh lean PMElementaryParticles.<module>`.
Compile it with `./build.sh fast PMElementaryParticles.<module>`.
Run `./build.sh audit` and `./build.sh e8p` for audits and reporter checks.
