# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md). Machine-layer organization is in
[Machine/REVIEW-AND-NEXT.md](Machine/REVIEW-AND-NEXT.md).

**Extension** marks a stronger result beyond the present theorem scope. **Certificate** marks an
external calculation awaiting formal verification. Each current theorem states its hypotheses.

## Substrate premises

None open.

The protocol register (which E8 structure carries protocol identity) is Paper III's application, not
a PMAction premise: PMAction supplies the constraints (`ColourRegister`: colour is a separate factor,
not the carrier axes), the factor construction (`IndependentRegisters`) and the stationary even sector
(`EvenComplement`). It is tracked in PMElementaryParticles REVIEW.

## Extensions

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
  results are in [OVERVIEW](OVERVIEW.md). Derive the native firing law on
  the encoded rest states and the rates it induces. The serial endpoint and
  elapsed time alone leave the pulse winding free.
  The first-row comparison is downstream in
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#first-row-wall-leakage).
  Recorded comparison tension (not a constraint on the derivation): with
  weights fitted to recorded masses, the first-row comparison prefers
  `r ≲ 0.07–0.12`, below the explored `1/8 ≤ r ≤ 1/2`
  (PMElementaryParticles OVERVIEW, daughter channels). Derive `r` from the
  schedule first, then compare.
  The absolute clock is `p` (`Machine/RootTransferPhase`:
  quarter-time `π/(2 gap p)` ticks).
- **Label-sensitive comparison schedule.** `TollAmplitude` fixes the conversion: a label with
  Toll `T`, counted in expected registrations, keeps amplitude `exp(−T/2)` (`β c₀ = 1`). What
  remains is the schedule: which comparisons act on which labels, at which steps and how often.
  Derive it from the repair the wire needs, not from the mass ladder. On static hypercharge
  flags the conversion admits the charged order and any ratio
  (`PMElementaryParticles.ProtocolToll.survival_ladder`, `doubling_iff`).
  A static-flag schedule needs a hypercharge step outside the
  fifth-root window, `d < (5 − √5)/8` or `d > (5 + √5)/8`
  (`ProtocolToll.window_no_ladder`); the steps selected so far
  (`3π/4`, `k · 6π/5`) are inside it. The doublet-position readouts are outside it:
  the full readout `3π/2` and the lepton-only readout `π/2`
  (`ProtocolToll.full_readout`, `lepton_readout_iff`). Neither repeated
  visits nor auxiliary decoding can make shared diagonal hypercharge
  alone write an exact quark-position record from the persisting
  massive packet (`PMElementaryParticles.HeavyFlipRecords`). A
  generation-addressed endpoint control and exact signed-axis
  comparison have explicit charge phases and a root-orbit branch
  (`ElectricHeavyRecord`). Derive admission of the joint kick,
  bank allocation and clean seeds, and select the physical reference,
  tariff, placement and firing schedule. This is the common blocker of the
  PMElementaryParticles readout items and PMFlavor item 2.
- **Requirement table for events.** `RefreshSchedule` and `CoherentRefresh`
  prove that Economy serves each required item exactly once; the table is
  the input. For one charged-current event it is now derived
  (`PMElementaryParticles.EventRequirements`): the emission depends on the
  parent's doublet position and nothing else, so the event requires one
  bit. The quark bit is read only by the full readout (`3π/2`), the lepton
  bit by the full or the lepton-only readout (`π/2`). If each label pays
  only its own event's readout, `T_e = T_d` and `T_u = T_ν`
  (`own_event_tolls`): the table read label by label cannot order the
  charged labels. Shared accounting, first step: a persisting massive
  label is on both walls and its flag is the slot mean
  (`DiagonalReadout.state_flag`, `PMElementaryParticles.EventRequirements.massive_flag`);
  one full readout serves both bits, and it still ties the electron with
  down (`full_massive`). Open: the rest of the shared-register accounting. Which labels are
  present when a readout acts (the parent, the emitted pair on all four
  axes, the persisting packet), what writes the exact records, and how
  the flags accumulate into a persisting label's Toll. The same
  accounting serves the lightest masses' firing law and PMFlavor's
  in-cycle wall record.
- **Polarization continuum matching.** Compare the normalized primitive-period response tensor
  (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator
  limits. Sharpen the lattice remainder bound enough to compare it with
  `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits.** Establish joint-limit and operator-domain control for the integrated gauge
  Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and
  interacting-field estimates.

## Certificates

- **Carrier spectrum and radius.** Certify the lowest positive level of the full 216-dimensional
  operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are
  in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
