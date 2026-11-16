# PMFlavor — open work

Closed results and retired routes are in [OVERVIEW](OVERVIEW.md); what flavour is here and the terms
(wire, label state, protocol, event, `J`, `U`) are in [README](README.md).

**Purpose and rule.** PMFlavor finds `J`, the label-change amplitudes of one charged-current event,
for carriers off and on the reference axis. The observed matrices are `U_uᴴ J U_d`; `U` belongs to the
wire (PMAction) and the protocols (PMElementaryParticles). Every number comes from E8 structure or a
narrowly stated premise; data are only the final test (e8p). Do not fit integers or parameters to
data, and do not frame work as fitting Standard Model sectors.

**Status of each entry of `J`** (e8p readout names in brackets).

| Label change | Off the axis | On the axis |
|---|---|---|
| class `0`, `2 → 1`, in-cycle | `π/14` [`s₁₂`]: share candidate (`HalfTurnAperture`), readout rule derived (`ConductionRule`); **no source:** the refresh keeps the label (item 2) | the same rule gives `π/10`; e8p prints `1/(2φ) = sin(π/10)` [`sin²θ₁₂`] (decision pending) |
| class `2`, `1 → 0`, node, reference wall | no derived amplitude; the library's rules are excluded (`TransferAmplitude`) [`\|V_cb\|`, printed `(π+χ)/(α⁻¹−Dπ)`] | no construction [`sin²θ₂₃`, printed `(1+π/(ν+σ))/χ`] |
| class `1`, `0 → 2`, node, other wall | `1/(2α⁻¹+π)`: two-leg series path derived; boundary `π` a premise [`s₁₃`] | `3/α⁻¹`: one leg into three outlets, candidate (`ReactorConductance`) [`sin²θ₁₃`] |
| phase | none in the library [`δ = arctan(σ/χ)` printed] | derived from the angles (`ReferenceFlavour`) [`δ_PMNS`] |
| loss | `q² = 515/516`, derived under one premise (`DressingEvent`) | — |

## The chain behind each value in `Values` (2026-11-16)

What e8p prints is `PMFlavor.Values`. Each number's derivation status, so a comparison is read with
its chain in view (`CKM` docstring: the four CKM forms are supplied model formulas whose numerals are
derived invariants, `FlavourInvariants`):

| Value | Formula | Status | Where |
|---|---|---|---|
| `s₁₂` (`cabibbo`, `vus`) | `π/(ν−χ) = π/14` | share candidate; aperture premises; readout rule derived. No event source for the in-cycle change (`RefreshLabel`) | `HalfTurnAperture`, `ConductionRule` |
| `s₁₃` (`vub`) | `1/(χα⁻¹+π)` | two-leg series path derived; boundary `π` a premise; names consistent with the wire (`PMAction.WireMass`) | `VubSeriesPath`, `TransferAmplitude.jump` |
| `\|V_cb\|` | `(π+χ)/(α⁻¹−Dπ)` | supplied; no derived amplitude (library rules excluded) | `CKM`, `VcbEnvelope` (unbased) |
| `δ` | `arctan(σ/χ)` | supplied; no phase source in the library (item 5) | `CKM`, `CPPhases` |
| `A`, `ρ̄`, `η̄`, `J`, `sin 2β`, `γ` | from the four above | exact consequences (barred `ρ̄`, `η̄`: `WolfensteinBar.zbar_eq`) | `Wolfenstein`, `WolfensteinBar`, `TriangleAngles`, `TriangleGamma` |
| `q² = 515/516` | dressing | derived under one premise | `DressingEvent` |
| `sin²θ₁₂` | `1/(2φ)` | on-axis rule gives `π/10`; decision pending (item 3) | `PMNS`, `ConductionRule` |
| `sin²θ₂₃` | `(1+π/21)/2` | no construction (item 4) | `PMNS` |
| `sin²θ₁₃` | `3/α⁻¹` | candidate: one leg into three outlets | `ReactorConductance` |

So the close CKM numbers rest on two derived paths (`s₁₃`, the consequences) and on supplied forms
(`|V_cb|`, `δ`) and candidates (`s₁₂`, PMNS). The wire (PMAction) does not yet produce them: with the
derived carrier placement its singular values fail the up and lepton mass ratios for every `δ_O` and
cycle phase (PMElementaryParticles REVIEW, "Protocol readout"). Presenting the numbers needs this table
next to them.

## Open work

1. **`U` from the protocol readout (blocks the data tests below).** The observed matrix is
   `U_uᴴ J U_d`. On the derived wire (`PMAction.WireMass`) the heavy–light rotations are not small
   (`≈ 0.14` for down at its light ratio, numerical), and neither the linear nor the squared readout of
   the wire's spectrum fits the up and lepton protocols (PMElementaryParticles REVIEW, "Protocol
   readout"). Until the readout is derived, every comparison that assumes `U = 1` (items 2, 3, 5) is
   conditional, and the four CKM magnitudes constrain `(J, U)` jointly.
2. **The amplitude of each entry of `J`.**
   - In-cycle (`κ₀`): no event source (`RefreshLabel`). The share `π/14` rests on the aperture premises
     (`HalfTurnAperture`); with no source in the event it is a candidate for `U`'s 1–2 part or nothing.
   - Other-wall node change (the jump): series path derived; derive the boundary `π`.
   - Reference-wall node change: no derived amplitude; at `U = 1` it must be `≈ 10.7×` the jump
     (`CandidateTests.promo_rules_excluded`: the three library rules fail). `VcbEnvelope` has no
     schedule basis.
3. **Completion order inside one event.** `corner_split`: the two-step term splits as `w, 1 − w̄`; `w = ½`
   for any power series in `A`, `w = 0` for forward composition (FC). At `U = 1` with `κ₁ = jump`,
   Stewart's relation gives `w = 0` at `1.1σ`, `w = ½` at `4.9σ`, `w = 1` at `25σ`. Derive FC from the
   refresh acting on one wall one way round the cycle, or keep it as a named premise. Conditional on
   item 1.
4. **On-axis readouts (PMNS).** (a) `ConductionRule` gives `π/10` for the on-axis in-cycle change; e8p
   prints `1/(2φ) = sin(π/10)`. Derive the sine or switch (`PMNS`, `PMNSIntervals`, `FlavourInvariants`,
   e8p); JUNO separates them. (b) `sin²θ₂₃ = (1+π/21)/2` has no construction; `Theta23Wall`: a common wall
   factor cancels, so the reference-wall on-axis change needs an asymmetric factor. Data: NuFIT 6.0 with
   SK-atm puts `θ₂₃` in the lower octant (`0.470`), `6σ` from the printed `0.575`; without SK-atm `0.561`
   (`1.2σ`). (c) Re-derive the in-cycle / node split for states on axis `0` (`inCycle_iff` is for
   off-axis states).
5. **The phase.** Nothing in the library supplies one; a sourceless holonomy is flat (`FlatPersistence`).
   The only rephasing invariant of `J` is the cycle holonomy `Φ` (`cycle_invariant`). Candidates and
   status (OVERVIEW, "Where a CP phase can sit"): `0`, `π` (glue arithmetic, the refresh's spinor lift):
   flat, excluded at `U = 1`; `π/2`: the refresh is not a single-plane half-turn (`CPQuarterTurn`);
   `2π/3` (triality): no mechanism; the node phase: real (`TickPlacement`); a wall-side leg phase
   (`LinkFlux.flux_cyclic`): open. A per-protocol cycle phase in `U` is the other route; it needs item 1.
6. **Dressing outlets.** `DressingEvent.event_law_spatial` works on axis labels only; the on-axis node
   change's three outlets (`ReactorConductance`) and the dressing's three (`DressingChannels`) should be
   one count.
7. **Transfer selection.** `ReferenceSelection`, `RelativeFrameCost`, `TransferWorkLaw`, `TransferAmount`,
   `SpectralGapOrder`, `ChordBranch` run on `PMAction.FlavourEvolution` and are conditional until PMAction
   shows the substrate update acts on wall modes as `e^{−iHt}`.

## Data relations to explain (targets, not fits)

- Mixing tracks mass ratios: small CKM angles with hierarchical quark masses, large PMNS angles with
  mildly hierarchical neutrino masses.
- `|V_us| ≈ √(m_d/m_s)` (GST, `0.5σ`) and `|V_td/V_ts| ≈ 0.21`. With the derived placement the wire no
  longer gives this (`LightPairTexture` is the algebra of the withdrawn placement).
- `|V_cb| = 0.041` is below `√(m_s/m_b)` and `√(m_c/m_t)`; `|V_ub/V_cb| ≈ 0.093`.
- No charged-lepton square-root relation; the large PMNS angles point to the neutrino protocol.

## Cleanup

- Rename `FlavourPulls` (now only `weak_mixing_shared`) and `FlavourPostulates` (defines `φ`, `pi_b`,
  `sqrt5_b` in the `FlavourPulls` namespace), and the `Flavour…` transfer-selection modules. Replace
  "generation" by "label state" in docstrings as they are touched. `TransferGraph.mode`: rename to the
  in-cycle / reference-wall / other-wall changes.
- Candidate to retire: `TransferGenerator` (the Cayley completion: a power series in `A`, the `w = ½`
  case, excluded with the jump at `U = 1`; its equal-lead-width premise is not derived). It is cited in
  OVERVIEW ("The transfer is the Cayley form") and in `PMAction.WallHopPhase`, `MassInsertion`
  docstrings, so retiring it means rewriting those.
- Candidates to remove (no importers, superseded): `PerStepContract` (marked experimental),
  `CPQuarterTurn` (an excluded route; its lemmas are cited in item 5), `VcbEnvelope` (unbased; only
  `CandidateTests` uses it).

Working notes: avoid `simp` on a transposed matrix literal or a product of three literals; name the
intermediate literal and use `rfl` (`LinkKronComparison.Lcg_eq_transpose`). Numerical scans belong
outside Lean and are labelled external.
