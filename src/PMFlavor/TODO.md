# PMFlavor — open work

Closed results and retired routes are in [OVERVIEW](OVERVIEW.md); what flavour is here and the terms
(wire, label state, protocol, event, `J`, `U`) are in [README](README.md).

**Purpose and rule.** PMFlavor finds `J`, the label-change amplitudes of one charged-current event,
for carriers off and on the reference axis. The observed matrices are `U_uᴴ J U_d`; `U` belongs to the
wire (PMAction) and the protocols (PMElementaryParticles). Every number comes from E8 structure or a
narrowly stated premise; data are only the final test (e8p). Do not fit integers or parameters to
data, and do not frame work as fitting Standard Model sectors.

**Where the entries now stand.** `ReferenceRouting` gives a direct
in-cycle route and two node routes, whose common reference value is
`α/2` (`PMAction.ReferenceNode`). The glued register uses the signed
label for the weak partner, and the tagged in-cycle word acts on that
label. Derive how the node distinguishes the two weak partners and
gives unequal amplitudes (item 2).
[Wall orientation and weak refresh](OVERVIEW.md#wall-orientation-and-weak-refresh)

| Label change | Off the axis | On the axis |
|---|---|---|
| class `0`, `2 → 1`, in-cycle | `π/14` [`s₁₂`]: share candidate (`HalfTurnAperture`), readout rule derived (`ConductionRule`); an E8 root word gives the geometric edge with a wall record; native firing stays open (item 2) | the same rule gives `π/10`; e8p prints `1/(2φ) = sin(π/10)` [`sin²θ₁₂`] (decision pending) |
| class `2`, `1 → 0`, node, up member holds the reference's class | no derived amplitude; the library's rules are excluded (`TransferAmplitude`) [`\|V_cb\|`, printed `(π+χ)/(α⁻¹−Dπ)`] | no construction [`sin²θ₂₃`, printed `(1+π/(ν+σ))/χ`] |
| class `1`, `0 → 2`, node, down member holds it | `1/(2α⁻¹+π)`: two-leg series path derived; boundary `π` a premise [`s₁₃`] | `3/α⁻¹`: one leg into three outlets, candidate (`ReactorConductance`) [`sin²θ₁₃`] |
| phase | none in the library [`δ = arctan(σ/χ)` printed] | derived from the angles (`ReferenceFlavour`) [`δ_PMNS`] |
| loss | `q² = 515/516`, derived under one premise (`DressingEvent`) | — |

## The chain behind each value in `Values` (2026-11-16)

What e8p prints is `PMFlavor.Values`. Each number's derivation status, so a comparison is read with
its chain in view (`CKM` docstring: the four CKM forms are supplied model formulas whose numerals are
derived invariants, `FlavourInvariants`):

| Value | Formula | Status | Where |
|---|---|---|---|
| `s₁₂` (`cabibbo`, `vus`) | `π/(ν−χ) = π/14` | share candidate; aperture premises; readout rule derived. The E8 root word needs a wall record and a firing law (`InCycleEvent`) | `HalfTurnAperture`, `ConductionRule` |
| `s₁₃` (`vub`) | `1/(χα⁻¹+π)` | two-leg series path derived; boundary `π` a premise; names consistent with the wire (`PMAction.WireMass`) | `VubSeriesPath`, `TransferAmplitude.jump` |
| `\|V_cb\|` | `(π+χ)/(α⁻¹−Dπ)` | supplied; no derived amplitude (library rules excluded) | `CKM`, removed unbased envelope candidate |
| `δ` | `arctan(σ/χ)` | supplied; no phase source in the library (item 5) | `CKM`, `CPPhases` |
| `A`, `ρ̄`, `η̄`, `J`, `sin 2β`, `γ` | from the four above | exact consequences (barred `ρ̄`, `η̄`: `WolfensteinBar.zbar_eq`) | `Wolfenstein`, `WolfensteinBar`, `TriangleAngles`, `TriangleGamma` |
| `q² = 515/516` | dressing | derived under one premise | `DressingEvent` |
| `sin²θ₁₂` | `1/(2φ)` | on-axis rule gives `π/10`; decision pending (item 3) | `PMNS`, `ConductionRule` |
| `sin²θ₂₃` | `(1+π/21)/2` | no construction (item 4) | `PMNS` |
| `sin²θ₁₃` | `3/α⁻¹` | candidate: one leg into three outlets | `ReactorConductance` |

So the close CKM numbers rest on two derived paths (`s₁₃`, the consequences) and on supplied forms
(`|V_cb|`, `δ`) and candidates (`s₁₂`, PMNS). The wire's mass matrices cannot supply them (their
rotations keep `|V_cb| ≤ 0.010`, PMElementaryParticles OVERVIEW); `J` is the source. Presenting the
numbers needs this table next to them.

## Open work

1. **`U` from the protocol readout.** The observed matrix is `U_uᴴ J U_d`. On the derived wire the
   mass-matrix rotations are small for the heavy–light part (`|V_cb|`-size `≤ 0.010`) and depend on the
   lightest-mass offsets for the light pair (PMElementaryParticles REVIEW, "Lightest masses"); until
   those are derived, comparisons at `U = 1` (items 2, 3, 5) are conditional.
2. **The amplitude of each entry of `J`.**
   - In-cycle (`u–s`): `InCycleEvent` supplies the root word for `2 → 1`
     and a reversible light-pair completion on states with a wall record.
     Derive how the native update reads the wall record and fires the
     forward transition with its amplitude. `companion_decodes` recovers
     the wall bit from a companion in the other wall's class, using the
     retained-carrier representation in `PMAction.GenerationHistory`.
     Derive the preparation and update of that companion.
     The share `π/14` still rests on the aperture premises
     (`HalfTurnAperture`).
   - The two node edges: node value `α/2` (`PMAction.ReferenceNode`, `PMAction.PersistenceSelections` (1)). Derive the
     up/down-dependent factor between them (`≈ 10.7` at `U = 1`; the printed forms put `2(π+χ)` there)
     from a reference-node readout sensitive to the signed protocol label.
     The charge-weight comparison `(s_u/s_d)^p` requires `p ≈ 1.6`.
     Derive the boundary `π` of `|V_ub|`.
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
8. **Scale and orientation inputs.** Derive the unit anchors that turn dimensionful readouts into
   numbers (including the electron mass and the SI tick), and select the wall magnitude and the
   functional forms of the mixing relations. A cost depending only on squared mixing moduli ties the
   conjugate CP branches. Blocker: no scale-invariant cost singles out a scale along a nontrivial
   rescaling orbit, and the selection-symmetry results do not yet fix the orientation or the
   functional forms.

## First-row wall leakage

Close the row in dependency order. The PMKAutomaton and PMFlavor operator work
can proceed independently. The physical channel sum uses the resulting
external modes and current.

1. **PMKAutomaton.** Derive the native clock ratio `r = K_f/|y|` from the selected
   crossing and flip schedule in common time units. Check whether the actual
   generator has the off-diagonal rest form used for chiral pairing. The
   native one-wall lazy offset breaks that grading symmetry about any common energy.
   Glued support and stationarity still admit every positive ratio
   (`WallGapCalibration.arbitrary_cyclic_ratio`).
   [Clock work](../PMKAutomaton/TODO.md#absolute-timing)
2. **PMElementaryParticles (done).** The parent is the light mass
   eigenstate, the daughters are the light modes, and the gapped modes are
   closed channels by the spectrum's order (gap above the light band).
   [Daughter channels](../PMElementaryParticles/OVERVIEW.md#charged-density-and-wall-leakage)
3. **PMFlavor.** Build the native label-change event `J` on these states.
   `InCycleEvent` gives the geometric light-pair word and its wall-record
   requirement. `WeakCurrentBridge.modelCurrent_eq_PL` and
   `NativeFlavourCurrent.compressed` already give the chiral lift for a
   supplied label operator. Identify the selected event with that operator
   on the interacting modes. `RefreshLabel` preserves the label and the raw
   `EventTransfer.J` is isometric only at zero forward amplitudes. Derive the transition source and completion from the native
   event, or use a direct rate from its actual amplitudes. The outstanding
   amplitude and phase work is in items 2, 3 and 5. Derive the uniform
   outlet scalar on the same physical quark channels. Once derived, it
   factors through unequal contact weights by
   `DressingInheritance.calibrated_contact_deficit`.

**Comparison.** The outlet dressing alone gives `1/516 ≈ 1.94·10⁻³`.
`tools/first_row_readout.py` reports the wall-only deficit at about
`0.25 r²` for fitted wire weights and `0.08 r²` for equal weights, using
measured CKM entries and an unweighted light spectral window. The diagnostic
bounds `r ≲ 0.07–0.12` use the frozen comparison `(1.6 ± 0.7)·10⁻³`.
These numbers do not select the native schedule or external states.

## Data relations to explain (targets, not fits)

- Mixing tracks mass ratios: small CKM angles with hierarchical quark masses, large PMNS angles with
  mildly hierarchical neutrino masses.
- `|V_us| ≈ √(m_d/m_s)` (GST, `0.5σ`) and `|V_td/V_ts| ≈ 0.21`. With the derived placement the wire no
  longer gives this (`LightPairTexture` is the algebra of the withdrawn placement).
- `|V_cb| = 0.041` is below `√(m_s/m_b)` and `√(m_c/m_t)`; `|V_ub/V_cb| ≈ 0.093`.
- No charged-lepton square-root relation; the large PMNS angles point to the neutrino protocol.

## Cleanup

Done:

- `FlavourPulls` renamed to `SharedWeakMixing` (`weak_mixing_shared` only).
- `FlavourPostulates` renamed to `FlavourConstants`, namespace `PMFlavor.FlavourConstants`.
- `FlavourResponseSelection` → `LabelResponseSelection`.
- `FlavourOrderComparison` → `LabelOrderComparison`.
- `FlavourStationarity` → `LabelStationarity`.
- `TransferGraph.mode` constructors are `inCycle`, `referenceWall`, `otherWall`.
- `TransferGenerator` marked retired: excluded route; citing text in OVERVIEW,
  `WallHopPhase` and `MassInsertion` updated.
- `PerStepContract` removed.
- `VcbEnvelope` removed, including its use in `CandidateTests`.
- `CPQuarterTurn` kept: its cited lemmas remain in the file.

Remaining: none from this cleanup list. Any new flavor derivation work is in
the open items above.
