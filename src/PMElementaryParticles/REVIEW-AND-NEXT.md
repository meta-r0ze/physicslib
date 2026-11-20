# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records the checked operations. **[Premise]**
marks a physical identification or rule still to be derived.
**[Certificate]** marks a calculation awaiting formal verification.

## Isolated-excitation input and trace

A mass is the property of one isolated excitation on the vacuum. The sector
is fixed in `IsolatedExcitation`: a stationary E8 reference plus one packet
carrying a single 16-slot label. `occupiedInput_admitted` proves the valid
two-bank occupancy and `occupiedInput_supply`/`occupiedInput_acceptance` are
the existing supply and acceptance results. This is the definition of the
quantity, not a choice of O. The vacuum is a certified family
(`vacuum_nonunique`).

`IsolatedReceiverTrace` now separates the uniform control field from the
localized one. `uniformPorts` has six true bits when the packet is active and
fails the occupancy check (`uniformPorts_occupancy`); its zero flags under AND
and OR (`uniform_flag_zero_AND`, `uniform_flag_zero_OR`, `uniform_AND_OR_tie`)
are equal-arrival artifacts, not isolated-excitation results.
`localizedPorts x0 packet` has one live packet at `x0`, record vacuum there,
and vacuum elsewhere; its occupancy is one when active and zero otherwise
(`localizedPorts_occupancy`) and is preserved by `tick` under both rules
(`localized_occupancy_preserved`). The localized receiver flag and period sum
are not yet computed. The receiver registrations per period and the record bit
visits remain separate columns with no certified common ledger. The hold/FIFO
packet lifts move the bank but do not determine a booking tick set, so that
stop remains.

## Protocol readout blockers

EP inherits a [conditional Transport interface](../PMTransport/COMPONENTS.md#transport-closeout).
Its open inputs follow the [Transport ranking](../PMTransport/COMPONENTS.md#remaining-free-inputs-by-reach).
The supplied source, operation, read and cost must refer to the same trace.

| Ranked inputs | EP decision |
| --- | --- |
| G, T | Phase, requests and probe are named open controller fields in `ReceiverFields`. The localized receiver flag depends on the request field and is not yet enumerated. The hold/FIFO lifts do not determine booking ticks. |
| O, U, W | The isolated occupancy is vacuum plus one packet and is certified. `localizedPorts` places the live packet at one site and leaves the record stream at vacuum; the uniform control field is rejected by the occupancy check. General routing and writer attachment remain open. |
| K, B, D | The uniform control receiver column is zero by equal arrivals; it is not one excitation. The localized receiver column is not yet computed. The record bit-visit column is separate. General tariffs remain open. |
| J, Q, H, L | The localized embedding is one state family but its request field is still open. J, Q and L remain open. |

- **Heavy-label weight. [Certificate]** The isolated receiver trace gives
  zero registrations under both rules. The certified record columns colour
  `(2,1,0,1)` and lepton `(1,2,1,0)` remain separate and no isolated trace
  selects a physical record reference.
- **Lightest masses. [Premise]** Supply the admitted static selector
  and the charged offset on that leg. The
  [generation ledger](GENERATIONS.md#the-charged-lift) gives the exact
  conditional linear response. Its phase and route certificates
  do not set an inverse-period order. Derive the same calibrated
  generator before comparing to the first-row PMFlavor readout.
- **Species and neutral modes. [Premise]** The species assignments in
  `QuarkMasses`, `LeptonMasses` and `TierLedger` are a declared ledger.
  The localized trace has no address-to-tier bit, so it cannot replace the
  tier sets. For neutrinos, admit the
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
  (`tools/muon_radiative_certificate.py`). Radiative stage 2 has not been
  started: it must assemble the vertex, self-energy and real-emission diagrams
  and show the regulator logs cancel. Until stage 3, `MuonLifetimeCorrected`
  keeps the factor as a certified input, and the higher-order terms
  (`MuonQEDLoops`) stay supplied.

## Next EP priority

Run the localized embedding exhaustively over the 64 request fields and both
receiver rules. Then derive a booking tick set from a Transport lift, or name
the missing rule that selects which lift visits are booked.

## Does the eight-candidate family now differ numerically?

**Not established.** The only zero flag result in the tree is for the uniform
control field, which puts the packet on all sites and both streams and is not
one excitation. The localized one-excitation field has the correct occupancy,
but its receiver flag depends on the retained request field and has not been
enumerated.
