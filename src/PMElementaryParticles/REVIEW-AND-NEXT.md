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

**Reading the weight as a margin.** Relative to the bare wire, down is unmodified (`w_d ≈ 1`). If the
heavy-label weight is the minimum margin `W/k` (`PMSubstrate.MinimumMargin`, the substrate keeps no
more margin than persistence needs) and the correction gain `k` is the rate at which `β` carries the
heavy (vector-class) carrier to the reference axis, where it is compared with the reference, then the
library's crossing facts give `k_e : k_d = 1 : 1/3` (`PMAction.NativeDetuning.lepton_always_crosses`,
`colour_crosses_iff`, one colour pairing in three). The data need `k_d/k_e = 0.29–0.35` and
`k_u/k_e = 1/18.5–1/15.8` (scan). Premises not yet derived: gain = reference-visit rate, weight =
minimum margin on both walls' heavy entry.

**Up's gain, tried.** The channel inventory (`ProtocolInventory`, `PacketGaugeActions.flipWeak`):
left-handed channels are active (the weak refresh flips them every tick, up ↔ down, `ν ↔ e`),
right-handed ones static; the sterile vacancy is the reference carrier `+2e₀`. Under `β` a right-handed
up carrier on axis `2` lands on the vacancy (no protocol, held), a right-handed down carrier on `e_R`.
Counting corrective crossings per side gives up `0` (right) and `1/3` (left, through the flip to down):
averaged `k_u/k_e = 1/6`, product-type readings `0` or `∞`; none gives the data's `1/16–1/18`
(`w_u/w_d ≈ 5.4`). So "blocked crossing" alone does not set up's gain.

A second reading fits all three with one number: `ln w` is linear in the electric charge
(`w ∝ e^{cQ}`, `c ≈ 1.7` per unit charge, the same within the quark-scale spread for `e → d` and
`d → u`). That points at a charge-dependent maintenance cost of the heavy (vector-class) state, a
signed cost, i.e. relative to a background; Paper I's survival weight `exp(−β c)` would make it
exponential. Not derived.

What the library has for the charge reading (`PMConstants.Hypercharge`): the charges follow from flux
conservation and charge-balanced left/right couplings through a scalar of charge `h`, with
`Y_u = Y_q + h`, `Y_d = Y_q − h`, `Y_e = Y_l − h`, `Y_ν = Y_l + h` (up and `ν` couple through the scalar,
down and `e` through its conjugate). Since `Q = Y_R/2` for the right-handed channel, the charge reading
is `ln w ∝ Y_R = Y_L ± h`: a quark/lepton part (`Y_q − Y_l = 4/3`, `e → d`) and a scalar-orientation
part (`2h`, `d → u`). The library has no upkeep cost that depends on either; that cost is the missing
input.

**The resonance as a persistence choice** (`WireResonance.massless_iff`). `M` has a massless mode
exactly when `δ³ = −κ_O0κ_O1κ_O2`: three roots, the real `δ_c` and its rotations by `e^{±2πi/3}` (the
cycle phases of the earlier fits). All three give the same `m₂/m₃`. Premise to derive: the stationary
flip rate is the one that keeps a cost-free light mode. Numerically, with each quark protocol on a root
and weighted to its `m₂/m₃`: the same root for up and down gives `|V_us| ≈ 0.002`; different roots give
`|V_us| ≈ 0.26`, `|V_cb| ≈ 0.17`, `|V_ub| ≈ 0.027` (data `0.224`, `0.041`, `0.0038`).

**Next.** Derive the heavy state's upkeep cost per protocol (crossing reading: `w_d/w_e = 3`
exactly, up needs its own mechanism; charge reading: `w ∝ e^{(c/2) Y_R}` from one `c`). Derive the
resonance premise and which root each protocol takes, and the light masses as corrections. Until then
e8p's masses are the `QuarkMasses`/`LeptonMasses` tier ledgers, a declared assignment (their e8p
caveats say so). The tier ladder (`TierLedger`) is the same question in the paper's form.

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
