# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records checked results. **[Premise]** marks a
physical identification or update rule still to be derived from the E8
substrate. **[Calculation]** marks work within a specified model.

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

## Protocol register and coupling

- **Weak doublet and wall orientation. [Premise]** If Flavor's
  `OrientationDoublet` candidate is used for charged-current routing, exhibit
  a native encoding and update that identify reversal of the ordered wall
  classes with the weak-partner flip. The latter preserves the active bank
  in `ControlledGluedRegister`. The correspondence must specify how these
  actions agree on physical states, or the current needs a different
  register attachment.
  [PMFlavor current work](../PMFlavor/REVIEW-AND-NEXT.md#open-work)

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

- **Physical daughter channels for wall leakage. [Premise]** Identify the
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
