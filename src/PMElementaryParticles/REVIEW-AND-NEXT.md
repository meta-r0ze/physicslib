# PMElementaryParticles — open work

Done results are in [OVERVIEW](OVERVIEW.md). The wire (one light-mass form shared by every protocol)
is PMAction's; label changes are PMFlavor's.

## The protocol readout (first)

**Where it stands.** Reading a protocol's masses directly off the wire's spectrum
(`PMAction.WireMass`) fails: `PMAction.WireLightBound.eigen_ratio_bound` puts the light ratio at
`≥ k/√2 = 0.0026` (up's `m_u/m_c = 0.0021`), and numerically, with each protocol's own `δ_O` and
cycle phase, singular values fit down (no test) but not up (`m_c/m_t`: `0.022` against `0.0037`) or
leptons (`m_μ/m_τ`: `0.028` against `0.059`); squared singular values fail all three.
`CycleReadout`: steps that commute with the antipode cannot change this, so the readout needs an
antipode-odd step. On the wire there is none (`ProtocolReadout.odd_reference_no_split`); at the
channel layer the reference carrier `+2e₀` is one (`ReferenceHold`, whose wire test assumes the two
layers share the lepton heavy slot: `m_μ/m_τ` `0.028 → 0.038`).

**The resonance and the heavy-label weight** (`WireResonance`, `tools/protocol_readout_scan.py`).
`det M ∝ δ³ + κ_O0 κ_O1 κ_O2`: at `δ_c = −k^{2/3} ≈ −0.0237` the wire has an exactly massless mode, and
every protocol's light-ratio fit sits within a few percent of it, so the light ratios are offsets
from the resonance. On the resonance `m₂/m₃ ≈ 0.023` for every protocol (down's `0.020` is close). The
data need a weight `w` on the heavy label (both walls), `m₂/m₃ ≈ k^{2/3}/w`:
`w_e : w_d : w_u ≈ 1 : 2.9–3.5 : 16–18.5` (the spread is the quark-mass scale choice;
`w_e = 0.36`). Up and down differ, and the ordering follows the charge.

**Next.** Derive the heavy-label weight per protocol from what maintains the heavy (vector-class)
state each tick; this is the channel-layer coupling. Candidates already in the library, not yet
derived as weights: the `β` crossing fraction of the vector class (lepton `1`, colour `1/3`,
`PMAction.NativeDetuning`), which matches `w_d/w_e ≈ 3`; and `β` carrying the up protocol's carrier
onto the held reference and the down's onto the electron's (`BetaReference`), the only up/down
asymmetry found so far. Then derive why `δ_O` sits at the resonance, and the light ratios from the
offset. Until then e8p's masses are the `QuarkMasses`/`LeptonMasses` tier ledgers, a declared
assignment (their e8p caveats say so). The tier ladder (`TierLedger`) is the same question in the
paper's form.

Constraints any readout must meet are in OVERVIEW (`DoubletReflection`, `ProtocolReadout`,
`BetaReference`, `CoherentGate`): the partner asymmetry is first order for leptons and at least
second order for quarks; a readout that uses `β` needs a colour treatment first.

## Mathematical gap (Lean)

**Three-body phase-space factorization.** Derived from Lebesgue measure: the daughter's measure
`P/(4π²)` (`ElectronMeasure.width_from_lebesgue`), the pair's two-body volume `1/(8π)` at rest
(`PolarMeasure`), and the boost invariance of each massless leg's measure `d³k/|k|` and of the
two-leg measure (`NullBoost.measure_invariant`, `pair_invariant`). Open: the energy-momentum delta.
Show that for a test function `G` of the pair's total four-momentum
`∫∫ G(k̂ + k̂̄) F d³k/(2|k|) d³k̄/(2|k̄|) = ∫ d⁴Q G(Q) Φ ⟨F⟩_Q` over future timelike `Q`, by the
change of variables `(k, k̄) ↦ (Q, rest-frame direction)` (or, for fixed `Q⃗`, the energy cumulative
`∫ 1{|k| + |Q⃗ − k| ≤ t} F d³k/(4|k||Q⃗ − k|)` has `t`-derivative `Φ⟨F⟩`). Then
`MassiveDaughterSpectrum.pair_density` follows rather than being assembled.

## Other open work

- **Charged current to contact vertex.** Connect the charged-current operator to the contact vertex in
  `AmplitudeTrace` (external carrier states, mode weights, readout normalization).
- **Radiative factor.** `MuonLifetimeCorrected` supplies the one-loop QED factor; derive it as the soft
  photon dressing of the charged daughter.
- **First-row deficit as leakage** (`0.0016 ± 0.0007`). Show on the substrate that the charged current
  reads only the light part of a state (`ChiralLightBand`), so the gapped part `z` of
  `PMAction.LightLeakage` is weight lost from the row; then evaluate it with the wall gap from
  PMAction's wall evolution.
