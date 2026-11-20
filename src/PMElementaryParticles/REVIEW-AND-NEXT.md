# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records the checked operations. **[Premise]**
marks a physical identification or rule still to be derived.
**[Certificate]** marks a calculation awaiting formal verification.

## Protocol readout blockers

EP inherits a [conditional Transport interface](../PMTransport/COMPONENTS.md#transport-closeout).
Its open inputs follow the [Transport ranking](../PMTransport/COMPONENTS.md#remaining-free-inputs-by-reach).
The supplied source, operation, read and cost must refer to the same trace.

| Ranked inputs | EP decision |
| --- | --- |
| G, T | Clocked packet and pulse firing. This includes the heavy write, static insertion and shared guard placement. |
| O, U, W | Accessible writer traffic and its 16-slot embedding. State whether the reader consumes a routed value, retained record or booked comparison. |
| K, B, D | Which comparisons register, the paid work remaining after common jobs, and which exports pay erasure. |
| J, Q, H, L | Job reuse, ready references, the population and prior over visits, and successive-link dependence. |

- **Heavy-label weight. [Premise]** Admit both writer references on
  the same specified traffic and compare their complete paid work.
  [The schedule account](SCHEDULE.md#record-reference-remains-undetermined)
  gives the threshold and its scope. The colour-reference two-bit
  result gives the down geometric mean for a common bit price.
  Physical reference selection, the price per bit and the common
  heavy-flip factor remain open.
- **Lightest masses. [Premise]** Supply the admitted static selector
  and the charged offset on that leg. The
  [generation ledger](GENERATIONS.md#the-charged-lift) gives the exact
  conditional linear response. Its phase and route certificates
  do not set an inverse-period order. Derive the same calibrated
  generator before comparing to the first-row PMFlavor readout.
- **Species and neutral modes. [Premise]** The species assignments in
  `QuarkMasses`, `LeptonMasses` and `TierLedger` are a declared ledger.
  Transport does not identify the wire modes with those entries.
  For neutrinos, admit the static neutral partner and the coherent
  branch mixer in `BranchGateBoundary`. The paired Schur block
  requires unequal magnitudes of the reverse-cycle weights for a
  split from diagonal flips. See [the static vacancy](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
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
  (`tools/muon_radiative_certificate.py`). Remaining: formal verification
  in Lean. State the assembled kernel and the cancellation of the
  regulator logs (stage 2), then the Feynman-parameter integrals
  (stage 3). Until then `MuonLifetimeCorrected` keeps the factor as a
  certified input, and the higher-order terms (`MuonQEDLoops`) stay
  supplied.

## Next EP priority

Derive the heavy writer's admitted input and output on one clocked
trace. Identify its occupied source, its retained or exported record
and its booked comparison in the same state and phase. This targets
G, O, U and W together and supplies the population needed by the
paid reference comparison. The finite witnesses and experimental
references do not decide that trace.
