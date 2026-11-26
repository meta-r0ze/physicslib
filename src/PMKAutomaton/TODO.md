# PMKAutomaton — open work

See the [named premises](../../SCOPE.md#named-premises) and the [checked results](OVERVIEW.md).

## Reachable occupied background

- Construct the admitted vacuum/reference ⊗ one-packet successor and derive its controller requests and packet-bank operation from the reachable state (`ClockedRootTrials.historyCount`, `Components.jointTick`).
- Identify every executed record write, export and reset, its owner, and the restoring mode or input port; derive the ready supply instead of assuming a loaded train (`RecordSupply.clean_supply`, `OddReferenceSource.odd_seed_train_restores`).
- Prove restoration within the same 43-tick period with no intermediate resource deficit, and return the background/reference inventory to the certified stationary family (`BoundaryErasure.cycleErased`, `OddReferenceSource.rest_stationary`).

## Admission and ports

- Bind the retained requests, port arrivals and branch pulses in one admitted successor (`Components.jointTick`).
- Identify the occupied comparator and the live or record port that the consumer reads (`RingReceiver.receiver_flag_eq`).
- Admit the link and derive its through law conditional on the retained history (`Interface.Handoff.principal_through_area_eq`).

## Clock and accounting

- Identify the clock data retained by physical execution before imposing the full root-stabilizer invariance (`ClockSymmetry.swap_changes_clockReading`).

- Calibrate the root pulse on the substrate tick and select its principal branch (`RootClockCalibration.phase_alias_iff`).
- Specify allowed pulse overlaps and common-clock capacity for the admitted word (`Values.shortSerialTicks`).
- Supply detector support, booked visits and their price in common units (`LocalController.traceExchangeFlagCost`).
- Supply export ownership, disposal and the return connection (`BoundaryErasure.policy_cycle_counts_booked_exports`).
- Identify shared jobs by state, time and resource, and resolve contention (`RefreshSchedule.minimal_is_ledger`).

## Reference supply

- Identify the occupied incoming reference and its renewal at each accepted visit (`OddReferenceSource.odd_seed_train_restores`).
- Derive the accepted disturbance and tolerance for that supplied orbit (`OpenHandoff.acceptance_iff_supply`).
