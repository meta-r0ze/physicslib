# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records the checked operations. **[Premise]**
marks a physical identification or rule still to be derived.
**[Certificate]** marks a calculation awaiting formal verification.

## Isolated-excitation input and conditional mixed witness

A mass is the property of one isolated excitation on the vacuum. The sector
is fixed in `IsolatedExcitation`: a stationary E8 reference plus one packet
carrying a single 16-slot label. `occupiedInput_admitted` proves the valid
two-bank occupancy and `occupiedInput_supply`/`occupiedInput_acceptance` are
the existing supply and acceptance results. This is the definition of the
quantity, not a choice of O. The vacuum is a certified family
(`vacuum_nonunique`).

`IsolatedTrace` is **not** an isolated-input trace. It iterates the mixed
contention witness `mixedBasisRing` and books hand-defined hold/FIFO slot
sets. Its receiver and record terms have no certified common ledger. It is
kept, relabelled, as a conditional (mixed witness, hand-booked) account; its
`1, 1, 2, 2, 1, 1, 44, 44`, heavy columns, and down-identity theorems do not
report isolated-excitation values. The isolated-input trace remains to be
computed on a state built from `occupiedInput`.

## Protocol readout blockers

EP inherits a [conditional Transport interface](../PMTransport/COMPONENTS.md#transport-closeout).
Its open inputs follow the [Transport ranking](../PMTransport/COMPONENTS.md#remaining-free-inputs-by-reach).
The supplied source, operation, read and cost must refer to the same trace.

| Ranked inputs | EP decision |
| --- | --- |
| G, T | Clocked packet and pulse firing. The isolated receiver embedding and the lift-derived hold/FIFO tick sets are still missing. |
| O, U, W | The isolated occupancy is vacuum plus one packet and is certified. The embedded receiver requests, probe and port fields are open; an isolated-input trace must derive them or name them. |
| K, B, D | The current receiver and record columns are conditional and have no certified common ledger. General preparation, crossing, export and reset tariffs remain open. The retained ring erases nothing. |
| J, Q, H, L | H is not fixed until the isolated trace is computed; the current mixed witness is not that trace. J, Q and L remain open. |

- **Heavy-label weight. [Certificate]** The conditional mixed-witness account
  restates the certified record columns colour `(2,1,0,1)` and lepton
  `(1,2,1,0)`, but no isolated-input trace has run. The physical record
  reference remains open.
- **Lightest masses. [Premise]** Supply the admitted static selector
  and the charged offset on that leg. The
  [generation ledger](GENERATIONS.md#the-charged-lift) gives the exact
  conditional linear response. Its phase and route certificates
  do not set an inverse-period order. Derive the same calibrated
  generator before comparing to the first-row PMFlavor readout.
- **Species and neutral modes. [Premise]** The species assignments in
  `QuarkMasses`, `LeptonMasses` and `TierLedger` are a declared ledger.
  The conditional mixed-witness account has no address-to-tier bit, so it
  does not replace the tier sets. For neutrinos, admit the
  static neutral partner and the coherent branch mixer in
  `BranchGateBoundary`. The paired Schur block requires unequal magnitudes
  of the reverse-cycle weights for a split from diagonal flips. See
  [the static vacancy](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
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
  (`tools/muon_radiative_certificate.py`). Radiative stage 2 remains open. `RadiativeStage2` records only that the
  leading-log contact coefficient is zero; it does not assemble the vertex,
  self-energy and real-emission diagrams or show the regulator logs cancel.
  Until stage 3, `MuonLifetimeCorrected` keeps the factor as a certified
  input, and the higher-order terms (`MuonQEDLoops`) stay supplied.

## Next EP priority

Embed `IsolatedExcitation.occupiedInput` into `RingReceiver.State`, name any
underived controller field, iterate `tick` for one period under AND and OR,
and replace the hand-booked mixed-witness account with actual isolated-input
results.

## Does the eight-candidate family now differ numerically?

**Not for isolated excitations.** The only differing numbers are the
conditional mixed-witness, hand-booked rows. That account does not run
`occupiedInput`, and its hold/FIFO slot counts are definitions rather than
Transport lift results. Until the isolated-input trace is computed, AND and
OR may tie for every isolated mass and no trace-derived eight-candidate
difference is established.
