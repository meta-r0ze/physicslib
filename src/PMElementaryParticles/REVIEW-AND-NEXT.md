# PMElementaryParticles — open work

Done results are in [OVERVIEW](OVERVIEW.md). **[Premise]** marks a physical
identification or selection still needed from the substrate. **[Supplied input]**
marks a value or law used conditionally. **[Calculation]** marks unfinished
mathematics in a specified model. **[Comparison]** marks a diagnostic against
external values.

## The protocol readout (first)

PMAction supplies the shared light-mass form. The bare resonant wire has an
exact zero mode, and its numerical readout gives `m₂/m₃ = √(3/2) k` at
`k/K = α/2` ([OVERVIEW](OVERVIEW.md#protocol-readout)). PMFlavor owns the
charged-current transfer readout. **[Supplied input]** The species masses
reported by e8p use the tier assignments in `QuarkMasses` and `LeptonMasses`.
The wire-to-species readout is open.

- **Heavy-label weight. [Premise]** Derive the label-sensitive upkeep from a
  native operation and show how it sets the heavy-wire flip amplitude.
  The fixed weak/colour schedules, scalar odd readings and label-only root
  ladder are excluded in [OVERVIEW](OVERVIEW.md#protocol-toll-constraints).
  Derive a resource history or coherent response whose upkeep distinguishes
  the two weak partners differently in the lepton and colour sectors.
  **[Comparison]** Compare the resulting mass ratios with the recorded
  targets. The neutral comparison needs a neutrino mass mechanism.
  Pulse selection and timing belong to
  [PMAction](../PMAction/REVIEW-AND-NEXT.md).

- **Lightest masses. [Premise]** Identify a native register-dependent
  insertion on the charged wire and derive its coefficient. Derive a
  substrate constraint that pins or shares the common detuning.
  [OVERVIEW](OVERVIEW.md#lifting-the-resonant-zero) records the exact lift
  for a supplied insertion and the independent-retuning obstruction.
  **[Premise]** For neutrinos, derive the physical vacancy projection and
  the dynamics that generates splittings beyond the label-preserving
  Dirac link.

## Other open work

- **Radiative factor. [Supplied input]** `MuonLifetimeCorrected` uses the
  finite one-loop coefficient in `q = 1 − (α/2π)(π² − 25/4)`.
  `MuonLifetimeHigherOrder` also uses supplied finite-mass and two-loop
  coefficients and the running-coupling prescription. `MuonRadiativeLog`
  proves the leading contact log vanishes in the charge-retention order.
  **[Premise]** Match the regulated continuum electromagnetic current
  and emission measure to the native E8 update.
  **[Calculation]** Derive the virtual vertex and self-energies with a
  photon-mass regulator using `PMAction.LoopMeasure`. Derive real emission
  in the same convention, combine the kernels to cancel the regulator,
  and evaluate the finite `q²` integral for comparison with `25/4 − π²`.
  The tree invariant-mass measure and the endpoint logarithmic integrals
  are in [OVERVIEW](OVERVIEW.md).

- **Physical daughter channels for wall leakage. [Premise]** Map the
  protocol labels in `FinalChannels` to interacting positive-energy
  daughter modes for the quark row and the muon calibration. At exact
  resonance, derive the parent preparation from the external-state
  dynamics. Stationarity permits every charged fraction in the one-leg
  family. Establish how the native current acts on those modes and use its
  channel amplitudes in the weighted rate sum.
  [OVERVIEW](OVERVIEW.md#charged-density-and-wall-leakage) records the
  charged-density normalization, the unweighted paired-window conversion,
  and the exact contact weight for supplied final masses. The paired-window
  conversion applies to the off-diagonal rest model. If the native generator
  retains a one-wall lazy offset, use its actual spectrum.
  [PMAction](../PMAction/REVIEW-AND-NEXT.md#extensions) tracks the pulse
  allocation and the effective flip-to-crossing ratio.
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#first-row-wall-leakage) now has
  the `InCycleEvent` root word for the active `2 → 1` edge. The companion
  carrier's class supplies the wall distinction in the oriented encoding.
  The native preparation and control of that record, the event's firing
  law and amplitude, and the full first-row comparison remain there.
