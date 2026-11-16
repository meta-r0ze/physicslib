# PMElementaryParticles — open work

Done results are in [OVERVIEW](OVERVIEW.md). The wire (one light-mass form shared by every protocol)
is PMAction's; label changes are PMFlavor's.

## The protocol readout (first)

**Where it stands.** The wire's light mass is one definition (`PMAction.WireMass`, carriers placed by
single-wall glue arithmetic). Its inputs are forced or do not fix the data (PMAction OVERVIEW, "The
wire's inputs"). Reading a protocol's masses directly off the wire's spectrum fails:
- `PMAction.WireLightBound.eigen_ratio_bound` (Lean): for `δ_O ≥ 0` the lightest-to-middle ratio is at
  least `k/√2 = 0.0026`; up's `m_u/m_c = 0.0021` is below it.
- Numerically, with each protocol's own `δ_O` and cycle phase: masses = singular values fits down (two
  numbers, two parameters, no test) but not up (`m_c/m_t`: `0.022` against `0.0037`) or leptons
  (`m_μ/m_τ`: `0.028` against `0.059`); masses = squared singular values fails all three.

So the readout is not "a protocol's masses are the wire's singular values". It has to be derived,
not chosen. A protocol's persisting states are stationary under everything that acts on it every
tick: the wire (odd sector), the weak refresh (the antipode on the pair, `PMFlavor.RefreshLabel`,
`DoubletSign`), and colour and hypercharge maintenance (`PMConstants.CarrierActions`).

**One refresh cycle with antipode-commuting steps** (`CycleReadout`, OVERVIEW). If every step
commutes with the antipode, the cycle (wire, then refresh) is `(−W_odd) ⊕ E` for any even action
`E` (`cycle_block`, `cycle_pow`), and its characteristic polynomial factors
(`cycle_charpoly`). So the odd sector's stationary states and phases are the wire's own: the
one-cycle readout is the direct readout, which fails. Every native word and the refresh commute
with the antipode. So a readout that departs from the wire's spectrum needs a step with an
odd/even block, and the only antipode-odd object is the reference carrier (`+2e₀`, vector class,
lepton axis). The even complement's action matters only through such a step.

**Next.** The step is the reference's maintenance: a reference-conditioned native update. This is
the same object as PMAction REVIEW "Other-wall detuning" (derive the wall-1 flip from a
reference-conditioned native update). Derive its action on the doublet over one cycle; by
`BetaReference.onto_reference_iff` it reaches the heavy label of the lepton axis directly and the up
protocol's heavy label on the paired axis through `β`. Then test it on the three charged
protocols' two mass ratios each, with no parameter beyond each protocol's `δ_O`. Until then e8p's
masses are the `QuarkMasses`/`LeptonMasses` tier ledgers, a declared assignment (their e8p caveats
say so).

**Constraints any readout must meet (Lean).**
- `DoubletReflection.flip_doublet`, `flip_keeps_reference_axis`: an observable invariant under the
  doublet reflection gives the two partners equal values; an up/down difference needs a
  reflection-odd response (`4 Re⟨A, B⟩` for exchanged amplitudes `A ± B`).
- `ProtocolReadout`: partners differ only by the odd/even cross term; the reference projector gives
  it at first order on the lepton axis only. So the partner asymmetry is first order for leptons and
  at least second order for quarks (the data agree: `ν`/`e` far more split than up/down).
- `BetaReference`: a fixed `β` on the carrier-axis index splits colour (PMAction REVIEW, "Colour and
  `β`"); a readout that uses `β` needs a colour treatment first.
- `CoherentGate`: unequal gate angles on a weak pair need one full bit of doublet position per event.

## Margin and Map

- The Boolean Map requires one clear live bit on each active payload row per visit
  (`visitRoute_active_clean_injective`, `visitRoute_collision`), the same for every protocol, so
  protocol differences enter through the gate (how often or how strongly the word fires).
- The minimum margin is `W/k` (`PMSubstrate.MinimumMargin.persists_of_margin`); what sets a protocol's
  correction gain `k` is open. Candidates, not derived: gain as visit rate, or as a record-orbit period
  (`marked_payload_return`). Earlier numerical margins per protocol used the withdrawn placement and
  must be redone on the derived wire before use.
- Open: which physical event enables the full active-bank antipodal word and when its output is read.
- Quarter turn: with both records set `pairVisit` has period 4 (eigenphases `±1, ±i`), the partners
  offset by half a period; whether a quarter turn attaches to one protocol needs a readout.

## Mathematical gaps (Lean)

### A3. Three-body phase-space factorization
The three-body measure is used but not factored. Target: factor it into
(pair invariant mass) × (pair angular measure) × (spectator energy), and derive the
`MassiveDaughterSpectrum` density `pair_density` as a *consequence* rather than an
input. This is the concrete mathematical content of former review item 2.
Uses the two-body phase-space result.

### A4. Massive neutrino pair
The massive pair tensor (`MassivePair`) and the massive two-body volume `2P/Q` (`MassiveVolume`) are
done. Open: the daughter-energy integral of `MassiveDaughterSpectrum`/`MassiveWidth` with this tensor
and volume, i.e. `pair_density`/`closed_width` for a massive neutrino pair (at least equal masses or
one massive leg), with positivity and endpoint limits.

### A5. Rotation invariance of the continuum angular average
Rotations about the polar axis and `z ↦ −z` are done (`ContinuumPair`). Open: rotations that move the
polar axis (they mix `z` and `φ`); identify `ContinuumPair.average` with Mathlib's sphere measure and
use its isometry invariance, so the pair tensor's covariance follows from the measure for every
integrable test function, not only from degree-≤2 moments.

## Other open work

- **Tier ladder.** `TierLedger` (`Δ⁰…Δ³`, up `{0, 2, 3}`, down and lepton `{0, 1, 2}`): derive the
  placement of each protocol's three label states.
- Connect the charged-current operator to the contact vertex in `AmplitudeTrace` (external carrier
  states, mode weights, readout normalization).
- Physical tick calibration for `DecayLaw`.
- Radiative factor: `MuonLifetimeCorrected` supplies the one-loop QED factor; deriving it (the soft
  photon dressing of the charged daughter) is open.
- The finite-channel replacement for the muon continuum phase space; the tau's electronic branching
  fraction is still an input; hadronic channels are PMHadrons'.
- A neutrino-decay prediction needs a physical channel and mass ordering (PMCosmology for
  propagation).
- First-row deficit as leakage (`0.0016 ± 0.0007`): needs the premise that `LightLeakage`'s `z` is the
  discarded outgoing current amplitude.
