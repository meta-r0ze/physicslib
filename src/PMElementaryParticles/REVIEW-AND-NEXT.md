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
[PMAction tracks the schedule](../PMAction/REVIEW-AND-NEXT.md#extensions).
The Toll-to-amplitude conversion is established in `PMAction.TollAmplitude`.

## The protocol readout (first)

The species masses reported by e8p currently use the tier assignments in
`QuarkMasses` and `LeptonMasses`. Derive the wire-to-species readout and use
the recorded mass ratios to check it.

- **Heavy-label weight. [Premise]** Derive a label-dependent heavy-to-node
  coupling ratio from E8.
  - Implement the joint electric kicks and supply a clean coordinate
    seed for the [root decoder](OVERVIEW.md#electric-decoder-on-the-odd-coordinate-bank).
    Prepare the other-wall companion and admit its joint update
    with the live root.
  - Select the physical comparator. Derive its registration tariff,
    including which labels participate in each visit and what record
    export or reuse costs. The
    [primitive phase ledger](OVERVIEW.md#primitive-flags-of-the-short-electric-decoder)
    prices preparation and the forward word from an occupied seed
    under unit flag pricing and gives the charged order at bit-reversed
    ports. If the cost enters through the reference node,
    derive the price for a crossing that carries a protocol label
    (`HandoffAdmittance.closure_one_price` assumes indistinguishable
    signals).
  - Derive the placement, rates and firing cadence on the two physical
    wall insertions. The [short decoder’s frame bound](OVERVIEW.md#short-root-decoder-and-serial-frame-bound)
    constrains fresh serial preparation. The [crossing and clock exclusions](OVERVIEW.md#primitive-crossing-activity-and-clock-limits)
    delimit what the bare glued roots and period can supply. Then test the
    derived charged ladder and Toll gaps against `tools/heavy_toll_targets.py`.

  See the [hypercharge constraints](OVERVIEW.md#protocol-toll-constraints),
  [record exclusion](OVERVIEW.md#record-comparisons-and-heavy-flip-toll), and
  [comparison diagnostics](OVERVIEW.md#other-heavy-weight-diagnostics).

- **Lightest masses. [Premise]** For the charged states, derive a
  native law that admits and fires a charge-selective coherent flip.
  Derive its pulse area and whether the same real detuning is held by
  a stationary calibration channel shared across charged protocols.
  [Charged insertion](OVERVIEW.md#charged-insertion-on-the-static-wall)
  gives selectors and the exact lift for the candidate on the static
  vector-class leg. A protocol-blind pulse area with the selector's unit
  amplitude inserts the same `ε` for each charged protocol, so on the
  substrate the protocols differ only if the area or amplitude depends on
  the protocol. Under the derived conversion that is a protocol-dependent
  Toll, `ε ∝ exp(−T/2)`, from the same schedule as the heavy-label
  weight. (Comparison only: the offsets matched to recorded ratios differ
  by about `50×` across protocols.) Derive the physical placement and use the selected
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
