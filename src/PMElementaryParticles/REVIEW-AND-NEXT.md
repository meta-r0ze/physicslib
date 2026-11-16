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
not chosen. **What persistence fixes, to derive it from:** a protocol's persisting states are
stationary under everything that acts on it every tick:
1. the wire, on the odd sector (`PMAction.FullCarrierIdentification`; `DoubletSign`);
2. the weak refresh, the doublet exchange, which keeps the label (`PMFlavor.RefreshLabel`);
3. colour and hypercharge maintenance (`PMConstants.CarrierActions`).
The refresh swaps partners every tick, so one protocol's state is not stationary under it alone; what
persists is the doublet over one refresh cycle, read through `ProtocolReadout`'s odd/even cross term.

**Next.** Write the one-cycle evolution (wire, then refresh) for a doublet, find its stationary states
and their phase advance per cycle, and state the readout that follows. Then test it on the three
charged protocols' two mass ratios each, with no parameter beyond each protocol's `δ_O`. Needs the
action of the even complement (PMAction REVIEW, "The even complement").

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

### A4. Massive neutrino pair (extend the daughter spectrum) — tensor done
Done (`MassivePair`): the rest-frame tensor of a pair with masses `m₁`, `m₂` from the same angular
symmetries (`massive_rest_tensor`), its covariant form `Q²⟨k₁k₂⟩ = Φ(P²/3) g Q² + Φ(E₁E₂ − P²/3) q q`
(`massive_rest_covariant`), the massless limit (`massless_limit`), two-body kinematics and shells.
Open: the massive two-body volume (`2P/Q` times the massless one) as a measure statement, and the
daughter-energy integral of `MassiveDaughterSpectrum`/`MassiveWidth` with this tensor.
`MassiveDaughterSpectrum`/`MassiveWidth` treat a massless neutrino pair. Target:
extend `pair_density`/`closed_width` to a massive neutrino pair (at least equal
masses or one massive leg), with positivity and endpoint limits, reusing the
transported pair tensor with `q² ≠ 0`. Closed form or a controlled integral.

### A5. Rotation invariance of the continuum angular average — partly done
Done (`ContinuumPair.average_rotate_polar`, `average_reflect_polar`): invariance under rotations about
the polar axis (any `f` periodic in `φ`) and under `z ↦ −z` (any `f`), no integrability needed. Open:
rotations that move the polar axis (they mix `z` and `φ`; needs the sphere change of variables, or the
identification of `average` with Mathlib's sphere measure and its isometry invariance).
`ContinuumPair` proves moments and linearity on *continuous* test functions but not
full rotation invariance for every integrable test function. Target: prove the
uniform-sphere average is invariant under rotations on `L¹` (change of variables /
Haar invariance of the sphere), so the pair tensor's covariance is a consequence of
the measure, not only of degree-≤2 moments.

## Other open work

- **Tier ladder.** `TierLedger` (`Δ⁰…Δ³`, up `{0, 2, 3}`, down and lepton `{0, 1, 2}`): derive the
  placement of each protocol's three label states.
- **`QuarkMasses`, `LeptonMasses`.** e8p's quark and lepton masses come from these modules' formulas,
  not from the wire. Connect them to the wire through the readout above, or state them as supplied.
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
