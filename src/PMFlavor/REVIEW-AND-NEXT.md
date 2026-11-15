# PMFlavor — open work

Closed tests and retired routes are recorded in [OVERVIEW](OVERVIEW.md).

**Scope.** PMFlavor shows how information transfers between generations on the E8 substrate, and
that the transfers give the CKM and PMNS matrices, with values `e8p` can output. Not here: the wire
and its mass form (PMAction: `ReferenceWallMass`, `GenerationWalls`, `NativeFlavourWall`,
`FlavourEvolution`); how species appear and propagate (PMElementaryParticles); comparisons with
measurement (`tools/e8p/E8PConstants/PMFlavor`). Rule: every number comes from structure or from a
narrowly stated premise; data are only the final test. Do not fit integers or parameters to data.

**Status of each output** (the formulas are `CKM.lean`, `PMNS.lean`; `e8p` outputs them via
`Values`, `PMNSIntervals`, `Wolfenstein`, `TriangleAngles`):

| Output | Formula | Status |
|---|---|---|
| `s₁₃ = \|V_ub\|` | `1/(χα⁻¹ + π)` | path derived: two node legs and a boundary in series (`KronSeries`, `LinkKronComparison.two_leg_from_incidence`); amplitude = path admittance is a premise |
| `s₁₂` | `π/14` | candidate (`HalfTurnMixing`, `HalfTurnAperture`; premises listed there) |
| `\|V_cb\|` | `(π + χ)/(α⁻¹ − Dπ)` | candidate formula, no mechanism (`VcbEnvelope`) |
| `δ_CKM` | `arctan(σ/χ)` | supplied, no mechanism |
| `sin²θ₁₂` | `1/(2φ) = sin(π/10)` | candidate (`GoldenGeometry`, `HalfTurnMixing`) |
| `sin²θ₂₃` | `(1 + π/(ν + σ))/χ` | supplied, no construction |
| `sin²θ₁₃` | `(σ − χ)/α⁻¹ = (D − 1)/α⁻¹` | candidate: node conductance into the spatial outlets (`ReactorConductance`) |
| `δ_PMNS` | sum rule | derived from the other three angles (`ReferenceFlavour`) |
| dressing | `q² = 515/516` | derived under one premise (`DressingEvent`, `DressingInheritance`) |

## Information transfer on E8

- **Type each mixing element by its transfer (replaces the retired `TransferFlavor`).** The library
  has the transfer topology: root moves conserve the generation label, so mixing is a single-wall
  carrier move of the shared class (`PMAction.GenerationLabel`); exactly one generation pair mixes
  in-cycle and two must cross the reference node (`ExchangeAxis`); the two node crossings differ by
  the wall their class sits on (`ExchangeChirality`); a node crossing is a series admittance
  (`KronSeries`). `PersistenceMechanics.InformationTransfer` has the three modes (boundary
  conduction, capacity promotion, coordinate jump) but nothing ties them to E8 transfers. Write
  down, for each CKM and PMNS element, its transfer on the generation–class incidence graph, its
  mode, and the amplitude rule that follows (in-cycle aperture or node series path). Note: the
  library derives a 1 + 2 split (one in-cycle, two node crossings); whether the two node crossings
  are two different modes, as the paper's promotion (`|V_cb|`) and jump (`s₁₃`) say, is to be
  derived from `ExchangeChirality`, not assumed.
- **Generator or finite rotation: one rule.** `s₁₂ = π/14` uses the generator (the aperture value
  itself), while `sin²θ₁₂ = 1/(2φ)` is the finite rotation `sin(π/10)`; the generator would give
  `π/10`. `HalfTurnAperture` reads both as the same half-turn aperture, so the rule must be the same
  for both, or the difference derived (amplitude for quarks, probability for leptons,
  `NodeElimination`). Falsification: JUNO separates `π/10` from `1/(2φ)`.
- **`|V_cb|`** (`VcbEnvelope`, candidate): `env 1 / env (Δ − D)` or the unit-source divider. The tick
  reading has no schedule basis (`RequirementRows` assigns sectors to rows, no service-time map).
  To derive it, exhibit the schedule and count its unused ticks; separately identify the drive or the
  terminals.
- **The CKM phase.** No source in the library: every candidate searched is closed (OVERVIEW, "Where
  a CP phase can sit"); `FlatPersistence` makes a sourceless holonomy flat. A new premise must give a
  generation-space holonomy with offset other than `0` or `π`; state it narrowly and test it by the
  triangle angle `α` and `J` it predicts. Sign: the wall-naming convention (`LinkFlux`,
  `ReferenceFlavour.column2_difference_conj`).
- **`θ₂₃`** (the lepton `s`/`c` parity breaking). No construction. `Theta23Wall`: a wall factor common
  to both readouts cancels (`common_wall_cancels`), so a construction must supply a `μ`–`τ`
  asymmetric generation factor; `μ` and `τ` reach the reference through different class vertices
  (`s`, `c`). The octant is not settled by data (NuFIT 6.0 with and without the SK atmospheric data).
- **Dressing outlets** (`PMConstants.FlavourDressing` consumes it). `DressingEvent.event_law_spatial`
  works on axis labels only. Open: whether the CKM loss realizes that event law (zero rate on the time
  label, equal shares on the three spatial labels) and the row-to-outlet identification. The same
  three spatial outlets appear in `sin²θ₁₃ = (D − 1)/α⁻¹`; derive both from one outlet count.
- **The transfer reading** (`TransferGenerator`: CKM as zero-energy scattering `S(K_cc)`). Demoted:
  with the wire's couplings it gives `K₁₃ = K₂₃`. Decide in the element-by-element audit whether it
  survives as the amplitude rule for node crossings or is retired; its equal-lead-width premise is
  not derived.

## Transfer selection

- **Conditional on `e^{−iHt}`.** The transfer-cost chain (`ReferenceSelection`, `RelativeFrameCost`,
  `TransferWorkLaw`, `TransferAmount`, `SpectralGapOrder`, `ChordBranch`) is built on
  `PMAction.FlavourEvolution`. It becomes unconditional when PMAction shows the substrate update acts
  on wall modes as `e^{−iHt}` (PMAction REVIEW, "Update as `e^{−iHt}` on wall modes").

## Cleanup

- **`FlavourPulls`** now holds only `weak_mixing_shared` (and `FlavourPostulates` defines `φ`, `pi_b`,
  `sqrt5_b` in its namespace); rename both to what they are when the transfer typing lands.
- **Names.** Several transfer-selection modules carry `Flavour` names for transfer content
  (`FlavourOrderComparison`, `FlavourResponseSelection`); rename when the transfer typing lands.

Working notes: there is no Lean toolchain in the device shell; ask Kate for `./build.sh fast
PMFlavor`. Avoid `simp` on a transposed matrix literal or a product of three literals; name the
intermediate literal and use `rfl` (`LinkKronComparison.Lcg_eq_transpose`). Numerical scans belong
outside Lean and are labelled external. When editing these files by slicing between two anchors,
check that nothing between them is lost.
