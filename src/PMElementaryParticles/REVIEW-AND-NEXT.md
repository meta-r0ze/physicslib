# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records the checked operations. **[Premise]**
marks a physical identification or rule still to be derived.
**[Certificate]** marks a calculation awaiting formal verification.

## Isolated-excitation trace (closed for the mass object)

A mass is the property of one isolated excitation on the vacuum. The sector
is now fixed in `IsolatedExcitation`: a stationary E8 reference from
`RegisterVacuum`, `CarrierVacuumSector` and `NativeReferenceBackground`, plus
one packet carrying a single 16-slot label. `occupiedInput_admitted` proves
the valid two-bank occupancy and `occupiedInput_supply`/`occupiedInput_acceptance`
are the existing supply and acceptance results. This is the definition of the
quantity, not a choice of O. The vacuum is a certified family
(`vacuum_nonunique`), so the trace carries the smallest relevant family: the
two certified record references, lepton and colour.

`IsolatedTrace` runs one full 43-tick period. Electron booked Tolls in
candidate order (hold/FIFO × AND/OR × two placements) are
`1, 1, 2, 2, 1, 1, 44, 44`; amplitudes are `exp(-T/2)`. The trace registers
the receiver comparison and the two exact electric record bits; the retained
ring exports nothing, so every erased-bit count is zero. The heavy writer
gives down-label Tolls `(K+1)` for colour and `(K+2)` for lepton, where `K`
is the common receiver count. The colour trace satisfies
`s_d² = s_e · s_u` for every candidate; the lepton trace does not.

## Protocol readout blockers

EP inherits a [conditional Transport interface](../PMTransport/COMPONENTS.md#transport-closeout).
Its open inputs follow the [Transport ranking](../PMTransport/COMPONENTS.md#remaining-free-inputs-by-reach).
The supplied source, operation, read and cost must refer to the same trace.

| Ranked inputs | EP decision |
| --- | --- |
| G, T | Clocked packet and pulse firing. The isolated trace fixes the 43-tick receiver placement and shows that the two excursion placements do not change its per-period count. General pulse firing, the heavy crossing and the static insertion remain open. |
| O, U, W | The isolated occupancy is vacuum plus one packet and is certified. The embedding of general writer traffic and its 16-slot routing remain open. The trace's reader consumes the retained receiver flag and the stored record bit, not a routed general value. |
| K, B, D | The isolated booked Toll is now trace-derived: receiver visits plus the certified two-bit record. General preparation, crossing, export and reset tariffs remain open. The retained ring erases nothing. |
| J, Q, H, L | H is fixed for the isolated mass (one deterministic trace, no prior). J, Q and L remain open for sustained supply, shared jobs and successive links. |

- **Heavy-label weight. [Certificate]** The trace supplies the two certified
  record columns, but not which one is physical. Colour gives
  `(2,1,0,1)` and lepton `(1,2,1,0)` on the same trace. The colour column
  gives the down geometric mean; the lepton column does not. The remaining
  input is the physical record reference, not the paid work.
- **Lightest masses. [Premise]** Supply the admitted static selector
  and the charged offset on that leg. The
  [generation ledger](GENERATIONS.md#the-charged-lift) gives the exact
  conditional linear response. Its phase and route certificates
  do not set an inverse-period order. Derive the same calibrated
  generator before comparing to the first-row PMFlavor readout.
- **Species and neutral modes. [Premise]** The species assignments in
  `QuarkMasses`, `LeptonMasses` and `TierLedger` are a declared ledger.
  The isolated trace has no address-to-tier bit, so it does not replace
  the tier sets; it only books a label Toll. For neutrinos, admit the
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
  (`tools/muon_radiative_certificate.py`). Stage 2 now formalizes the
  assembled kernel and the cancellation of the regulator logs in
  `RadiativeStage2`; the Feynman-parameter integrals (stage 3) remain.
  Until stage 3, `MuonLifetimeCorrected` keeps the factor as a certified
  input, and the higher-order terms (`MuonQEDLoops`) stay supplied.

## Next EP priority

Identify which certified heavy record reference—colour or lepton—the
physical writer uses. That is the only remaining binary input in the
trace-derived heavy Toll and down identity. After it, derive the
address-to-tier map so the three trace Tolls can be assigned to the
declared generation rows.

## Does the eight-candidate family now differ numerically?

Yes, in the booked Toll and amplitude, and only through the two structural
coordinates that survive the trace. The hold/FIFO bank motion changes the
number of booked receiver visits (1 versus 43), and AND/OR changes the flag
(0 versus 1). The two excursion placements do not change the per-period
count, because the 43-phase clock is cyclic and both placements book the same
visit count. The heavy writer adds the reference difference: colour gives
down Toll `K+1`, lepton `K+2`. The tier sets still do not differ by candidate
and remain premises.
