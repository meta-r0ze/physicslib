# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records checked results. **[Premise]** marks a
physical identification or update rule still to be derived from the E8
substrate. **[Calculation]** marks work within a specified model.

None of these items blocks the downstream libraries: PMHadrons and later use the tier-ledger masses
(`QuarkMasses`, `LeptonMasses`), the E8 `G_F` and `α`, and the supplied lepton QED
(`MuonQEDLoops`). The tau's `B_e` without a supplied value is PMHadrons' "tau inclusive hadronic
factor" item.

**Common blocker.** The heavy-label weight, lightest masses and PMFlavor
item 2 need a native law that admits and fires a conditioned coherent pulse.
[PMTransport tracks slot bounds and firing branches](../PMTransport/CLOCK.md).
[PMAction tracks event admission](../PMAction/REVIEW-AND-NEXT.md#extensions).
The Toll-to-amplitude conversion is established in `PMAction.TollAmplitude`.
The [finite selection result](SCHEDULE.md#selection-and-the-unresolved-minimum)
requires a physically admitted family and its remaining costs.

## The protocol readout (first)

The species masses reported by e8p currently use the tier assignments in
`QuarkMasses` and `LeptonMasses`. Derive the wire-to-species readout and use
the recorded mass ratios to check it.

- **Heavy-label weight. [Premise]** Derive the admitted writer traces
  for both references. The open handoff can restore an identical
  reference for any supplied live sequence. The missing traffic
  input is the writer's booked population, including the treatment
  of the vacancy. The [lifecycle comparison](SCHEDULE.md#record-reference-remains-undetermined)
  then needs the signed difference of paid work after matching
  common jobs. Derive the fresh record supply and encoding, which
  pulse and reset flags register, and which export, renewal and
  maintenance jobs are already paid. Use the
  [label-sensitive schedule](../PMTransport/REVIEW-AND-NEXT.md#label-sensitive-handoff).

  The two-bit colour record gives the down geometric mean at any
  common bit price (`down_geometric_mean`). Its physical selection,
  price per bit and common heavy-flip factor remain open. Compare
  the derived gaps only after those quantities follow.
  See the [hypercharge constraints](OVERVIEW.md#protocol-toll-constraints),
  [record exclusion](OVERVIEW.md#record-comparisons-and-heavy-flip-toll), and
  [comparison diagnostics](OVERVIEW.md#other-heavy-weight-diagnostics).

- **Lightest masses. [Premise]** For the charged states, derive a
  native law that admits and fires a charge-selective coherent flip.
  The [generation comparison](GENERATIONS.md#the-charged-lift) excludes
  the shared route counts as the source of the protocol dependence. The
  candidate uses the same static vector leg and two comparisons for each
  charged protocol. `ChargedInsertion.det_flip_at_resonance` proves the
  same linear determinant response to the supplied offset. Derive an
  admitted record write, export and reuse schedule and its coupling to
  both the heavy and light pulses. The
  [phase and handoff calculation](GENERATIONS.md#phase-handoff-and-toll)
  gives zero flags on the matched input in both comparisons. The single
  vacancy-relative visit gives a one-to-two flag ratio. If that visit's
  survival weight sets the light pulse, its price must grow
  logarithmically in the period to give inverse-period powers.
  Derive the offset's order and determine whether an unmodified
  calibration channel maintains the same real detuning for all three
  protocols. Use the selected generator to derive the light-pair
  rotations in [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#open-work).
  Compare singular values with recorded ratios after the derivation.
  The [uniform-to-local check](OVERVIEW.md#lifting-the-resonant-zero)
  gives the determinant conversion and its spectral limits.
  For neutrinos, derive native admission of the phase gates and coherent
  branch mixer in `PMAction.BranchGateBoundary`, and route the retained
  occupied branch onto the static light wall. Use the
  [vacancy preparation](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
  as the candidate circuit for the vacancy-truncated model. For a Dirac
  mass, derive the native update that uses the reference scalar link to
  populate the static neutral partner. Derive neutral flips and crossings
  that split the masses. For diagonal flips, the
  [paired Schur block](OVERVIEW.md#equal-class-gapped-crossing) requires
  unequal magnitudes of the three reverse-cycle weights.

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
  (`tools/muon_radiative_certificate.py`). Remaining: formal verification
  in Lean. State the assembled kernel and the cancellation of the
  regulator logs (stage 2), then the Feynman-parameter integrals
  (stage 3). Until then `MuonLifetimeCorrected` keeps the factor as a
  certified input, and the higher-order terms (`MuonQEDLoops`) stay
  supplied.
