# PMElementaryParticles

EP classifies programs on the E8 node machine and checks conditional decay widths.
It builds on PMSubstrate, PMAction, PMConstants and PMKAutomaton. PMFlavor follows EP.

The [overview](OVERVIEW.md) maps programs, nested roles, declared ledgers, charges and decay.
`NestedFermion` gives the proposed level-0 through level-3 pillar roles and conditional
capacity/encoding results. `LedgerLevels` proves exact tower identities for the supplied
species footprints. It does not derive those ledgers or select physical level budgets.
`Muon` audits one level-1 charged lepton: its unit-account price is proved, while
the held-unit set and parent charges remain open.
`LevelZeroFermions` identifies the primitive held event and the labelled channels.
`LedgerPillars` tests the six-slot hypothesis without deriving charges from residuals.
`ChannelRecord` certifies minimal channel encodings and conditional reference distances.
`MapMaintenance` prices once-per-bit comparisons; physical encoding, reference and native
readout remain open. These encoding-dependent costs are excluded as physical masses.
`AutonomousCensus` upstream uses native cycle averages; `ClockScaleBoundary` states the
conditional clock conflict without choosing a physical tick duration.
The [open list](TODO.md) starts with complete level-0 realizations and their open prices. The
[scope ledger](../../SCOPE.md#named-premises) records shared premises.

`PMElementaryParticles.Values` exports the public masses, unit conversions and lifetime APIs.
Measured tau inputs enter only in e8p. The physical mass reading is upstream
`PMSubstrate.OccupancyCost.cost`; species counts and residuals remain supplied.

Check a module with `./build.sh lean PMElementaryParticles.<module>`.
Compile it with `./build.sh fast PMElementaryParticles.<module>`.
Run `./build.sh audit` and `./build.sh e8p` for audits and reporter checks.

Persistent targets are photon, electron, then proton. The timed Boolean electron
candidate and the collision-only binding obstruction are [mapped in the overview](OVERVIEW.md#persistent-targets-photon-electron-proton).
