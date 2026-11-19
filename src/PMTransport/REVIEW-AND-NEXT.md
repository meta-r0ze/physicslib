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
occupied seed required by root loading. The
[odd rest-mode loader](OVERVIEW.md#odd-rest-modes-as-occupied-reference-candidates)
gives a reference compatible with the odd carrier sector, while
parity-preserving root phases exclude the old single-label reference from an
odd source. Derive the occupied input population and axis selection from
the accessible vacuum family, or give an explicit reversible renewal step.
Admit the wall loader and the spatial translation. Use the acceptance
criterion to derive the viability margin against stated disturbances.

Derive the handoff law for labeled traffic and for successive nodes. The current
conductance theorem identifies the through weight for the stated two-stream
model. A law for a label-sensitive crossing needs a physical comparison and
its tariff. A law for successive handoffs needs the conditions that justify
multiplying through weights.

## Absolute event clock

Use the [clock ledger](CLOCK.md) for the certified results and timing
premises. Derive durations and prices in hop-time units for the crossing,
in-wall carrier and flip, and the coherent controls (`ClassBlindFlip`,
`RootCliffordCompletion`, `CompletedCarrierPhase`, `SelectiveCarrierRouting`).
Derive the generation and chirality controls, physical pulse areas,
wall-rate normalization and firing cadence. Use them to calculate the
light-band error and the finite-tick split update (`LightLeakage`,
`WallGapCalibration`, `SplitClockBoundary`). If the native schedule retains
a one-wall lazy offset, use the spectrum with that offset for the daughter
calculation (`NativeWallOffset.rest_offset_breaks_chirality`).

The [whole-tick alias result](OVERVIEW.md#calibrating-the-root-clock) applies
  even to the full integer-tick coherent history. The reference excursion
  supplies consecutive trial slots on the same E8 root. A shared request
  cancels, and the independent-trial statistic requires joint true-true
  weight `p²` at equal marginals `p`. Derive that law for the physical
  requests and establish that the admitted coherent pulse uses the same
  elapsed time, or derive a physical first-half-turn bound and calibrate
  its coherent comparison. Use that rate in the shared firing schedule.
  The first-row comparison is downstream in
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#first-row-wall-leakage).

## Label-sensitive handoff

- **Seed and admission.** Supply an occupied odd coordinate seed in the
  predecessor glue class. The coordinate-zero first-wall candidate is
  a unit-population rest mode when supplied. Admit and place the
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
