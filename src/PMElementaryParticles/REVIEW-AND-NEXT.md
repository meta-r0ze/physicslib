# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records checked results. **[Premise]** marks a
physical identification or update rule still to be derived from the E8
substrate. **[Calculation]** marks work within a specified model.

None of these items blocks the downstream libraries: PMHadrons and later use the tier-ledger masses
(`QuarkMasses`, `LeptonMasses`), the E8 `G_F` and `α`, and the supplied lepton QED
(`MuonQEDLoops`). The tau's `B_e` without a supplied value is PMHadrons' "tau inclusive hadronic
factor" item.

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
  Tip: `ProtocolToll` shows a fixed relabeling schedule priced by changed
  labels gives weak partners equal Tolls, so the cost must depend on the
  label's state, not an event count. The heavy generation's two walls read
  the label in two class frames (classes `g + 1` and `g − 1`, related by
  triality): in the vector frame the sign is the doublet and the axis is
  lepton or colour; in a spinor frame sign and axis mix. A cost built from
  the label's overlap with the reference in both frames together (for
  example their product) has the odd `×` even form the constraints require.
  Test it against the `≈ ×3` ladder `u, d, e, ν` before building more.

- **Lightest masses. [Premise]** For the charged states, derive a
  native law that admits and fires a charge-selective coherent flip.
  Derive its pulse area and whether the same real detuning is held by
  a stationary calibration channel shared across charged protocols.
  [Charged insertion](OVERVIEW.md#charged-insertion-on-the-static-wall)
  gives selectors and the exact lift for the candidate on the static
  vector-class leg. Derive the physical placement and use the selected
  generator to determine the light-pair mass-basis rotations in
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#open-work).
  For neutrinos, derive native admission of the phase gates and coherent
  branch mixer in `PMAction.BranchGateBoundary`, and route the retained
  occupied branch onto the static light wall. Use the
  [vacancy preparation](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
  as the candidate circuit. Derive a neutral mass operator that gives the
  prepared sector a spectrum with mass splittings for oscillations.
  Tip: screen any candidate first against the off-resonance offsets the
  data need (`e 0.038`, `d 0.14`, `u 0.0024`; OVERVIEW, protocol readout).
  They follow no single law in charge, so a shared mechanism must produce
  that pattern; `ResonanceLift` already shows a free common detuning would
  restore the zero, so what holds it fixed is part of the derivation.

## Protocol register and coupling

- **Weak doublet and wall orientation. [Premise]** If Flavor's
  `OrientationDoublet` candidate is used for charged-current routing, exhibit
  a native encoding and update that identify reversal of the ordered wall
  classes with the weak-partner flip. The latter preserves the active bank
  in `ControlledGluedRegister`. The correspondence must specify how these
  actions agree on physical states, or the current needs a different
  register attachment.
  [PMFlavor current work](../PMFlavor/REVIEW-AND-NEXT.md#open-work)
  Note: the obstruction `ControlledGluedRegister.no_protocol_preserving_wall_exchange`
  comes only from the two positive lepton channels, which the inventory
  names "neutrino" (active wall) and "sterile vacancy" (static wall). A
  wall exchange pairs a left-handed channel with its right-handed partner,
  as a Dirac mass does, so this is `ν_L ↔ ν_R`. The crossing preserves the
  label and charge (`opposite_label`, `opposite_charge`); requiring the same
  base-protocol name on both walls is too strong. Restate the requirement as
  label and charge preservation, with the static positive lepton read as
  `ν_R` when the crossing acts; this also feeds the neutrino part of
  "Lightest masses". The `OrientationDoublet` part applies only if Flavor
  uses that candidate.

## Other open work

- **Radiative factor. [Premise]** Match the regulated continuum
  electromagnetic current and emission measure to the native E8 update.
  **[Calculation]** Use `PMAction.LoopMeasure` to obtain the virtual vertex
  and external self-energies with a photon-mass regulator. Derive real
  emission in the same convention, cancel the regulator in the inclusive
  rate, and integrate the finite one-loop kernel over the pair invariant.
  Compare its massless-electron coefficient with `25/4 − π²`. The corrected muon lifetime and its use in the
  [PMHadrons channel inventory](../PMHadrons/OVERVIEW.md#channel-inventory-and-interfaces)
  currently use supplied QED inputs, including the higher-order terms.
  Tip: before formalizing the virtual and real parts in Lean, write a
  numerical certificate of the whole chain in the charge-retention form
  (`tools/`) and confirm `25/4 − π²`; it catches convention errors cheaply.
  `RadiativeIntegrals` (`Li₂`) and `PairInvariantSpectrum` (the `q²`
  spectrum) are the first steps. Keep the **[Premise]** (native matching)
  separate so the **[Calculation]** can finish on its own.

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
