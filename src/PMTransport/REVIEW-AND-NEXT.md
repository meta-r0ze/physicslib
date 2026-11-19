# PMTransport — open work

The [overview](OVERVIEW.md) records the checked results and their hypotheses.

## Node handoff

Use the [checked two-site handoff](OVERVIEW.md#two-site-handoff-and-the-six-pillars)
as the local execution trace. It fixes both destinations, the closed-pair
return, and the comparison flags for the two visits. Derive the physical
admission of the spatial hop and receiver exchange, the source of the
incoming occupied reference, and the branch trigger. Calibrate the elapsed
time against the substrate clock. Select the physical registration tests
and add paid registrations to the same trace as the derived state flags.

For repeat operation, the
[open-route trace](OVERVIEW.md#open-route-and-reference-supply) gives a
nearest-neighbour D₄ line, the record destinations, and the exact incoming
reference population required for any finite horizon. The basis-reference
route uses a different prepared upstream slot per visit and specifies the
occupied seed required by root loading. Derive the physical admission
of the translation and the supply of those seeds, or give an explicit
reversible renewal step. Use the acceptance criterion to derive the
viability margin against stated disturbances.

Derive the handoff law for labeled traffic and for successive nodes. The current
conductance theorem identifies the through weight for the stated two-stream
model. A law for a label-sensitive crossing needs a physical comparison and
its tariff. A law for successive handoffs needs the conditions that justify
multiplying through weights.

## Absolute event clock

- **Absolute event clock.** Durations of the native events in hop-time units and their relation to
  the substrate tick: the crossing rate `y`, the in-wall carrier and flip rates, and the timing and
  price of the native control circuits (`ClassBlindFlip`, `RootCliffordCompletion`,
  `CompletedCarrierPhase`, `SelectiveCarrierRouting`). The leading light-mass
  ratios and routing are set by `k/K`, the resonance and the reference. It is needed for absolute
  scales, for converting node admittances into Hamiltonian rates (`CertainTransferRate`), for the
  light-band error at derived rates (`LightLeakage`; `WallGapCalibration` leaves the flip-to-crossing
  ratio free), and for the finite-tick walk (`SplitClockBoundary` excludes a single Hamiltonian
  exponential). A rate ratio needs less than the absolute clock: equal pulse
  areas and generator normalizations make it an inverse duration ratio on a
  common clock. `CertainTransferRate` gives the minimum certain-transfer pulse
  area, and selecting that branch for each event takes a native argument. The
  flip program is `32` root quarter-times (`ClassBlindFlip.forwardTimes_total`).
  The flip-to-crossing ratio, which the
  light-band leakage needs, also uses the crossing duration. Derive both effective
  rates on one schedule. `CertainTransferRate.common_tick_rate_ratio` cancels
  the common tick explicitly. Derive the native pulse areas, their conversion
  into the wall couplings and the firing cadence. A one-wall lazy offset
  rules out chiral anticommutation about every common energy
  (`NativeWallOffset.rest_offset_breaks_chirality`). If the native schedule
  retains it, use the resulting spectrum for the daughter calculation. The equal-class
  gapped support has a six-reflection word (`PMElementaryParticles.GappedGluedCrossing`):
  four for the factor swap and two amplitude-only parity reflections in the
  class frame. Derive the native generation/chirality selector for the coherent
  crossing and in-wall flip, the pulse timing and the firing schedule. For
  the class-changing crossing, moving a carrier between the generation's two
  wall classes takes three reflections (`tools/event_clock_check.py`; one for equal classes).
  `SplitClassBlindFlip` certifies the shorter twelve-pulse class-blind flip:
  24 quarter-times for exact completed beta. With one tick per quarter-time,
  it and a six-reflection serial word need 36 elapsed ticks. The remaining
  scheduler question is which phases can carry these controls: 36 fits the
  43-phase period, and exceeds 32 if every elapsed pulse tick requires a
  distinct active slot. The crossing as E8 reflections (`tools/event_clock_check.py`
  7): `3` to move one carrier between the generation's two wall classes, `4` to map one generation's
  whole wall sector, and at least `6` for a class-blind crossing like the flip program (a map taking
  every class `x` on one factor to `x + 1` on the other has `rank(1 − w) ≥ 6`; swap plus diagonal
  triality attains it). Under the library's own principles (certain events, two quarter-times per
  reflection, class-blind programs) the program-duration estimate gives
  `r = K_f/|y| = 12/24 = 1/2`. The explored program options span `1/8 ≤ r ≤ 1/2`.
  Exact diagonalization (`tools/event_clock_check.py` 8) shows the reduction survives this: at
  `r = 1/2` the light masses stay `18×` below the gap, `m₂/m₃` moves by `+7%` (`+2.5%` at `1/4`), and the
  heaviest light mode has `26%` of its weight on the gapped components. So `K_f ≪ |y|` is not needed for
  the light-mass form. The remaining schedule must fit the selected
  controls on the native clock. The checked sixteen-pulse flip's minimum
  is 64 whole substrate ticks for certain transfer, so the single 43-tick
  serial frame is excluded for that circuit. A serial six-reflection
  crossing on its clock raises the lower bound to 88 ticks. These timing
  results are in [the action overview](../PMAction/OVERVIEW.md). Derive the native firing law on
  the encoded rest states and the rates it induces. The serial endpoint and
  elapsed time alone leave the pulse winding free.
  The first-row comparison is downstream in
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#first-row-wall-leakage).
  Recorded comparison tension (not a constraint on the derivation): with
  weights fitted to recorded masses, the first-row comparison prefers
  `r ≲ 0.07–0.12`, below the explored `1/8 ≤ r ≤ 1/2`
  (PMElementaryParticles OVERVIEW, daughter channels). Derive `r` from the
  schedule first, then compare.
  The absolute clock is `p` (`PMTransport.Machine.RootTransferPhase`, with
  quarter-time `π/(2 gap p)` ticks).

## Label-sensitive handoff

- **Seed and admission.** Supply an occupied odd coordinate seed in the
  predecessor glue class. Admit and place the
  [triality preparation](../PMElementaryParticles/OVERVIEW.md#triality-preparation-on-the-companion),
  the [chiral-current kicks](../PMElementaryParticles/OVERVIEW.md#electric-kicks-from-the-chiral-register-current),
  and the joint guarded crossing and companion update. Derive the rate and
  firing cadence at both physical wall insertions. Include the one- and
  two-root companion setups and all remaining serial visits. The
  [frame bound](../PMElementaryParticles/OVERVIEW.md#short-root-decoder-and-serial-frame-bound)
  constrains the inverse-root setup, and the
  [crossing and clock exclusions](../PMElementaryParticles/OVERVIEW.md#primitive-crossing-activity-and-clock-limits)
  constrain the bare glued roots and period.
- **Registration and record lifecycle.** Select the physical comparator. Derive
  which labels participate in each visit and what registration, record export
  and reuse cost. The companion's class transport leaves charged records
  occupied. The [primitive decoder ledger](../PMElementaryParticles/OVERVIEW.md#primitive-flags-of-the-short-electric-decoder)
  and the [companion and current ledgers](../PMElementaryParticles/OVERVIEW.md#electric-kicks-from-the-chiral-register-current)
  give conditional costs for one registration per state flag, including the
  intervening root swap. If the price enters through the reference node,
  derive the price with the protocol label retained.
  `HandoffAdmittance.closure_one_price` uses indistinguishable crossings.
- **Requirement table for events.** Extend the
  [single-event requirement](../PMElementaryParticles/OVERVIEW.md#protocol-toll-constraints)
  to shared-register accounting. Determine which labels are present at
  each comparison, which records must be written or reused, and how the
  executed visits contribute to each persisting label's Toll. This also
  serves the lightest masses' firing law and PMFlavor's in-cycle wall record.

## Machine dependencies

PMAction and `PMTransport.Machine` use each other's finite proofs. If the machine
needs a separate build target, extract a common finite dynamics base first.
The boundary includes `StateIdentification`, `CommonResponse`,
`ChiralityConvention`, `InvolutionComparison`, `RestorationResponse`,
`SelectedSampling`, `SubstrateReflection`, and `GaugeRecordEmbedding`.
