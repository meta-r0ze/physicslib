# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records the checked operations. **[Premise]**
marks a physical identification or rule still to be derived.
**[Certificate]** marks a calculation awaiting formal verification.

## Isolated-excitation input and trace

A mass is the property of one isolated excitation on the vacuum. The sector
is fixed in `IsolatedExcitation`: a stationary E8 reference plus one packet
carrying a single 16-slot label. `occupiedInput_admitted` proves the valid
two-bank occupancy and `occupiedInput_supply`/`occupiedInput_acceptance` are
the existing supply and acceptance results. This is the definition of the
quantity, not a choice of O. The vacuum is a certified family
(`vacuum_nonunique`).

`IsolatedReceiverTrace` now separates the uniform control field from the
localized one. `uniformPorts` has six true bits when the packet is active and
fails the occupancy check (`uniformPorts_occupancy`); its zero flags under AND
and OR (`uniform_flag_zero_AND`, `uniform_flag_zero_OR`, `uniform_AND_OR_tie`)
are equal-arrival artifacts, not isolated-excitation results.
`localizedPorts x0 packet` has one live packet at `x0`, record vacuum there,
and vacuum elsewhere; its occupancy is one when active and zero otherwise
(`localizedPorts_occupancy`) and is preserved by `tick` under both rules
(`localized_occupancy_preserved`). Requests are retained
(`localized_requests_retained`) and the localized port field has period 12
(`portStep_period_twelve`), so the 43-tick sum is three periods plus seven
ticks (`localizedSum43_eq`). The sum depends only on the exchange pattern
(`localizedSum43_eq_pattern`, `patternSum`). AND and OR differ exactly when
their pattern-table entries differ (`localized_and_or_differ_iff`,
`sumsDiffer`). Simultaneous rotation of packet site and requests leaves the
sum unchanged (`localizedSum43_rotate`); for fixed requests it can depend on
`x0` (`localizedSum43_x0_depends`). An inactive packet gives zero
(`localizedSum43_inactive_zero`). The receiver registrations per period and
the record bit visits remain separate columns with no certified common ledger.
The hold/FIFO packet lifts move the bank but do not determine a booking tick
set, so that stop remains.

### Homogeneous requests and ring size

**Unconstrained least Toll (Task F, Steps 1–2).** On the 3-ring,
`localizedSum43_eq_zero_iff_empty` gives receiver sum zero iff the exchange
pattern is empty, and `localizedSum43_nonempty_ge_fourteen` gives every other
pattern at least 14. PM least Toll therefore selects the empty firing pattern:
AND selects request fields with no `(true,true)` site
(`and_zero_iff_no_true_true`); OR selects request fields with every site
`(false,false)` (`or_zero_iff_all_false`). An unconstrained isolated packet
never registers. On the 4-ring the same result is
`localizedSumN_four_zero_iff_empty`; the n=5 decision run did not finish within
ten minutes and was stopped at n=4.

**Label constraints (Task F, Step 3).** No certified result says a labelled
packet needs at least k *receiver* registrations. The existing requirements
are record/readout flags (`EventRequirements.massive_flag`,
`DiagonalReadout.state_flag`, `ElectricHeavyRecord.phase_position` /
`phase_sector`, `HeavyFlipRecords.orbit_record_tolls`,
`WireSchedule.bitToll`, `CoherentGate.unequal_needs_orthogonal`,
`GenerationWalls`). The missing link is a certified map from those
record/readout requirements to `RingReceiver.receiverFlag`; none is invented
here.

**Task I reference-background bit rings (hypothesis, not certified).** The
candidate vacuum is the reference record on both streams everywhere; a packet
replaces the live bits at one site. Each record bit has its own ring and
requests. The references are colour `(false,false)` (up record) and lepton
`(true,false)` (neutrino record). `bitToll_eq_hamming` and `colour_hamming`
reproduce the EP rows. Complement symmetry is `tick_complement` and
`receiverFlag_complement`. `bitRingEmbed` is the bit-ring state;
`bitRingEmbed_equal_zero`, `bitRingEmbed_background_fixed`,
`bitRingEmbed_false_true`/`bitRingEmbed_true_false` and `bitRingSum43_eq` give
the per-bit 43-tick result. `bitRingTotal43_eq` gives the total over the two
rings; `bitRingTotal43_shared` gives
`bitToll ref c * patternSum (firingPattern either r) x0`. Unconstrained least
Toll is zero for every label (`bitRingTotal43_empty_zero`); a zero-Hamming
label is zero for every request field (`bitRingTotal43_hamming_zero`). The
Task H encounter scaffolding was removed. This remains a hypothesis, not a
certified identification.

**Record writes are receiver flags (Task G, Step 1).** `record_step_identity`
on `RingReceiver.State n` equates the one-tick change in record occupancy with
exchanging `(true,false)` arrivals minus exchanging `(false,true)` arrivals;
`flagCountInt_eq` identifies the receiver flag count with the sum of those
counts. `record_step_abs_le` and `record_net_le_flagSum` give the one-tick and
T-tick absolute bounds.

**Task G, Step 2 outcome: (b).** `WireSchedule.bitToll` and
`HeavyFlipRecords.orbit_record_tolls` count `labelRecord` exact flags
(`ElectricHeavyRecord.phase_position`/`phase_sector`, `orbitBitPrice`). No
certified map identifies that record bit with a `RingReceiver` record-stream
port or with record occupancy. The gap-U objects are the
`WireSchedule`/`HeavyFlipRecords` record bit, the `ElectricHeavyRecord` exact
comparison flag, and the `RingReceiver` record-port value. Step 3 was not run.

**Achievable 43-tick sums (observation).** On the 3-ring the distinct sums
are `{0,14,15,21,22,43}` (`patternTable`, `localizedSum43_eq_pattern`). The
n=4 full 43-tick decide exceeded 600 seconds and was stopped; the n=4
zero/empty theorem `localizedSumN_four_zero_iff_empty` remains. These are
registration counts, not masses or tiers.

**Finding (Task E, Step 1).** Requests are independent initial data; no
certified relation to the reference background exists. `ClockedRootTrials`
takes the controller background `initial : Finset M` and the request
projection `requestOf : M → Bool × Bool` as separate supplied inputs
(`historyCount`), and its module states that the background and its request
projection are separate inputs. `LocalController` keeps requests in the
supplied register state; `RingReceiver` retains them; the native background
stores reference values, not requests. No map from the background
configuration to the request field is certified.

Consequently no certified result forces the retained request field to be
site-independent. `HomogeneousRouting.equivariant_is_translation` constrains
the routing permutation; `LocalController.radius_one` is local dependence.
Homogeneous requests are a named hypothesis (`HomogeneousRequests`), not a
derived result. Steps 2–3 of Task E were not run.

Conditional on that hypothesis, the four uniform requests are enumerated on
the 3-ring: `(false,false)` gives 0 under AND and OR; `(true,true)` gives 43
under both; a mixed request gives 0 under AND and 43 under OR
(`uniform_falsefalse_sums`, `uniform_truetrue_sums`,
`uniform_truefalse_sums`, `uniform_falsetrue_sums`).

The localized embedding and occupancy check are generalized to `Fin n`.
For `n = 3,4,5,6`, an empty uniform firing pattern gives zero at every tick
for any `T` (`empty_uniform_flags_zero`); a full uniform firing pattern gives
exactly one flag per tick in the 43-tick window
(`full_uniform_flag_count_three` … `_six`) and sum 43
(`full_uniform_sum43_three` … `_six`).

The register-per-tick case has the form of a direction flip each tick. The
Feynman-checkerboard reading of mass as the direction-flip rate is a
hypothesis for later, not a result of this library.

## Protocol readout blockers

EP inherits a [conditional Transport interface](../PMTransport/COMPONENTS.md#transport-closeout).
Its open inputs follow the [Transport ranking](../PMTransport/COMPONENTS.md#remaining-free-inputs-by-reach).
The supplied source, operation, read and cost must refer to the same trace.

| Ranked inputs | EP decision |
| --- | --- |
| G, T | Phase, requests and probe are named open controller fields in `ReceiverFields`. Requests are retained and enumerated by their exchange pattern. The localized 43-tick sum is `patternSum (firingPattern either r) x0`; AND and OR differ exactly when those table entries differ (`localized_and_or_differ_iff`). The hold/FIFO lifts do not determine booking ticks. |
| O, U, W | The isolated occupancy is vacuum plus one packet and is certified. `localizedPorts` places the live packet at one site and leaves the record stream at vacuum; the uniform control field is rejected by the occupancy check. The localized receiver flag is computed by `receiver_flag_eq`; the record Toll remains a separate column. General routing and writer attachment remain open. |
| K, B, D | The localized receiver sum is the `patternSum` table; the record bit-visit column is separate with no common ledger. General tariffs remain open. |
| J, Q, H, L | The localized embedding has one state family; the request field is an enumerated input, not a selected history. J, Q and L remain open. |

- **Heavy-label weight. [Certificate]** The isolated receiver trace gives
  zero registrations under both rules. The certified record columns colour
  `(2,1,0,1)` and lepton `(1,2,1,0)` remain separate and no isolated trace
  selects a physical record reference.
- **Lightest masses. [Premise]** Supply the admitted static selector
  and the charged offset on that leg. The
  [generation ledger](GENERATIONS.md#the-charged-lift) gives the exact
  conditional linear response. Its phase and route certificates
  do not set an inverse-period order. Derive the same calibrated
  generator before comparing to the first-row PMFlavor readout.
- **Species and neutral modes. [Premise]** The species assignments in
  `QuarkMasses`, `LeptonMasses` and `TierLedger` are a declared ledger.
  The localized trace has no address-to-tier bit, so it cannot replace the
  tier sets. For neutrinos, admit the
  static neutral partner and the coherent branch mixer in
  `BranchGateBoundary`. The paired Schur block requires unequal magnitudes
  of the reverse-cycle weights for a split from diagonal flips. See
  [the static vacancy](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
  and [the gapped crossing](OVERVIEW.md#equal-class-gapped-crossing).

## Other open work

- **Radiative factor. [Certificate]** The substrate's own order-`α`
  correction is derived numerically from the diagrams
  (`tools/muon_radiative_derivation.py`): the conserved wall vertex
  (`PMAction.SpinorVertex`, `Z₁ = Z₂` on the substrate), continuum photon
  modes, the virtual vertex and both self-energies, and real emission at
  fixed neutrino-pair invariant, with explicit ultraviolet, infrared and
  collinear regulators. The total is independent of each regulator and
  reproduces the inclusive kernel pointwise (`z = 0.1 … 0.9`, to `10⁻⁴`
  relative at `m_e = 3·10⁻⁴`), so its integral is `π² − 25/4`
  (`tools/muon_radiative_certificate.py`). Radiative stage 2 has not been
  started: it must assemble the vertex, self-energy and real-emission diagrams
  and show the regulator logs cancel. Until stage 3, `MuonLifetimeCorrected`
  keeps the factor as a certified input, and the higher-order terms
  (`MuonQEDLoops`) stay supplied.

## Next EP priority

Run the localized embedding exhaustively over the 64 request fields and both
receiver rules. Then derive a booking tick set from a Transport lift, or name
the missing rule that selects which lift visits are booked.

## Does the eight-candidate family now differ numerically?

**It can, conditional on G.** The localized receiver trace registers zero when
the exchange pattern is `000`; for every other exchange pattern the 43-tick
sum is a positive entry of `patternSum` (`localizedSum43_eq_pattern`). AND and
OR differ exactly when their exchange-pattern table entries differ
(`localized_and_or_differ_iff`). This depends on the retained request field,
which is the open controller input G; no request field or rule is selected.
