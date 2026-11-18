# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records checked results. **[Premise]** marks a
physical identification or update rule still to be derived from the E8
substrate. **[Calculation]** marks work within a specified model.

None of these items blocks the downstream libraries: PMHadrons and later use the tier-ledger masses
(`QuarkMasses`, `LeptonMasses`), the E8 `G_F` and `α`, and the supplied lepton QED
(`MuonQEDLoops`). The tau's `B_e` without a supplied value is PMHadrons' "tau inclusive hadronic
factor" item.

**Common blocker.** Three items (heavy-label weight, lightest masses, wall
leakage) and PMFlavor item 2 wait on one object from PMAction: the native law
that fires a conditioned coherent pulse. The conversion from a Toll to a wire
amplitude is now derived (`PMAction.TollAmplitude`: `exp(−T/2)` with `T` in
expected registrations). What is still open is the schedule: which
comparisons act on which labels, at which steps and how often
([PMAction extensions](../PMAction/REVIEW-AND-NEXT.md#extensions)). The
radiative factor does not depend on it.

## The protocol readout (first)

The species masses reported by e8p currently use the tier assignments in
`QuarkMasses` and `LeptonMasses`. Derive the wire-to-species readout and use
the recorded mass ratios to check it.

- **Heavy-label weight. [Premise]** Derive a native, label-sensitive upkeep
  rule and derive which heavy-wire flip amplitudes it changes and by how much.
  The rule must distinguish the two weak partners differently in the lepton
  and colour sectors. Use the
  [toll constraints](OVERVIEW.md#protocol-toll-constraints) to screen
  candidates. [PMAction](../PMAction/REVIEW-AND-NEXT.md#extensions) owns
  pulse selection and timing.
  Derive a reference-conditioned repair history or joint response on
  the four colour orbits. The Toll constraints give the affine bound
  for sums of static hypercharge comparisons against a fixed reference.
  PMAction supplies the selected repair schedule and the conversion
  from Toll to wire amplitude. Test the resulting protocol weights
  against the recorded ladder.
  The static bound excludes an affine conversion only, and the derived
  conversion is not affine. On the static flags it gives the charged
  order and any ratio (`ProtocolToll.survival_ladder`, `doubling_iff`;
  steps `π/2` and `3π/2` as a witness). The recorded ladder then needs
  Toll differences `T_e − T_d ≈ 2.0–2.3` and `T_d − T_u ≈ 2.9–3.0`
  expected registrations (`tools/protocol_readout_scan.py` weights at
  `k = α/2`). Derive the schedule in PMAction and then compare it with
  these differences. Do not choose steps or counts from them.

- **Lightest masses. [Premise]** For the charged states, derive a
  native law that admits and fires a charge-selective coherent flip.
  Derive its pulse area and whether the same real detuning is held by
  a stationary calibration channel shared across charged protocols.
  [Charged insertion](OVERVIEW.md#charged-insertion-on-the-static-wall)
  gives selectors and the exact lift for the candidate on the static
  vector-class leg. A protocol-blind pulse area with the selector's unit
  amplitude inserts the same `ε` for each charged protocol. The matching
  insertions are `0.110` (e), `0.364` (d) and `0.0072` (u). So the area
  or the amplitude must depend on the protocol. Under the derived
  conversion that is a protocol-dependent Toll, `ε ∝ exp(−T/2)`, from the
  same schedule as the heavy-label weight. Derive the physical placement and use the selected
  generator to determine the light-pair mass-basis rotations in
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#open-work).
  Compare the candidate's singular values directly with the recorded mass
  ratios. The [uniform-to-local check](OVERVIEW.md#lifting-the-resonant-zero)
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

- **Radiative factor. [Premise]** Match the regulated continuum
  electromagnetic current and emission measure to the native E8 update.
  **[Calculation]** Use the checked soft angular factor in
  `RadiativeIntegrals`. Derive the regulated virtual vertex and external
  self-energies, and the real-emission kernel at the same neutrino-pair
  invariant. Combine them before removing the photon-mass regulator.
  Most of the matching is in PMAction. The native current is the
  conserved D₄ vertex with an exact Ward identity (`FiniteVertex.ward`,
  `leg_ward`, `PolarizationContact.contact_ward`): the midpoint vertex
  with `sinc(a r·q/2)` root weights, which goes to the continuum vertex
  as `a → 0`. The emitted photon uses
  continuum modes (CONTINUOUS.md, Rule 2; `PolarMeasure`, `NullBoost`).
  The leading log is zero (`MuonRadiativeLog.retention_no_log`), so the
  total is UV finite. The open steps are: (1) the spinor form of the
  conserved vertex; (2) a cutoff bound for the vertex plus self-energy
  integrand, as `LeadingLog.leading_log` gives for the log. The exact
  Ward identity should cancel the `1/k⁴` terms at every `k`; prove that,
  and then the region near `1/a` gives only `O((a m_μ)²)`; (3) the
  calculation below.
  Check the resulting density against the
  [inclusive benchmark](OVERVIEW.md#inclusive-one-loop-muon-benchmark),
  then formalize the derivation with `PMAction.LoopMeasure`,
  `PairInvariantSpectrum` and `RadiativeIntegrals`. The corrected muon
  lifetime and its use in the
  [PMHadrons channel inventory](../PMHadrons/OVERVIEW.md#channel-inventory-and-interfaces)
  currently use supplied QED inputs, including the higher-order terms.

- **Physical daughter channels for wall leakage. [Premise]** Low priority:
  the first-row deficit is PMFlavor's `1/516` dressing
  (`PMFlavor.DressingInheritance`), so leakage only adds to it and its
  output here is a bound (`r = K_f/|y| ≲ 0.07–0.12` with the current
  estimate, `tools/first_row_readout.py`). Identify the
  interacting positive-energy modes for the `FinalChannels` labels in the
  quark row and muon calibration. Derive the physical parent preparation at
  exact resonance. [PMAction](../PMAction/REVIEW-AND-NEXT.md#extensions)
  supplies the native rest generator and pulse rates once derived.
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#first-row-wall-leakage) owns
  the native current, including how the companion record is prepared and
  updated and how the in-cycle edge fires with its amplitude. Match that
  current to the physical modes.
  **[Calculation]** Sum the resulting channel strengths with the
  [contact weights](OVERVIEW.md#charged-density-and-wall-leakage) and
  compare the quark row and muon calibration. Use the spectrum of the
  generator selected by PMAction, including any retained one-wall offset.
