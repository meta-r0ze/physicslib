# PMConstants — open work (todo)

This is the current dependency map. A certified value below is a consequence
of the specified formula/model; it is not automatically an unconditional
physical derivation from Finiteness, Conservation and Causality. Start with
`CurrentConstants.current_snapshot` for current values and
[`OVERVIEW.md`](OVERVIEW.md) for the module map.

## Constant-by-constant map

| Constant / family | What Lean currently checks | What the physical derivation still needs |
| --- | --- | --- |
| Structural integers D=4, Δ=43, ν=16, σ=5, χ=2; α | Paper I's inherited structural/admittance formulas and Paper III's certified α interval (0.007297352562, 0.007297352563). | Paper I's substrate, impedance and selection assumptions remain inherited; Paper III does not rederive them from bare persistence. |
| Overhead η=171/172 | Capacity/coding theorems, geometric axis balance, conditional reference-star maintenance and return-law minimization. | Physical register width/reference factorization, (maintenance is required: skipping it under drift fails, `ReferenceAxis.skipped_maintenance_fails`), and an actual preparation/sampling contract. `ContentWeight.economy_selects_intensive` proves a numerical ordering, not physical admissibility or selection. |
| Weak fraction s=1849/8295 ≈0.222905365 | End to end from the derived table (`TableConsequences.end_to_end`). Exact ledger arithmetic, controlled carrier comparison response and explicit weighted response indices. | The operator comparison for involution-phase words now has an exact marker-free circuit (`CarrierPhaseComparison`, Paper II `InvolutionComparison`), and a supplied two-cell spatial register has exact all-state semantics (`SpatialComparison`). Physical controlled-gate/phase admission, clean-cell allocation, preparation/repair work and the clock/spatial/wire requirements remain open. Nine forward phase calls are not a minimum primitive price. Raw uniform packet response gives 5547/37777, so current matching cannot be inferred from one common calibration. With the selected (uniform) preparation the W mass excludes that raw reading by >289σ and keeps the effective one within 1.3σ (`ReadoutAccounting.ledgers_are_effective`): the ledgers are effective stiffness, i.e. charge-unit normalized; the packet trace-form (unified) normalization gives the excluded raw value (`GeneratorNormalization`). A common reference carrier gives that exactly when it is the lepton doublet (`ReferenceCharge.equal_response_iff`); a shared colour-invariant reference is exactly L (`shared_colourless_reference_iff`); sharing follows from the single reserved cell that fixes η, and the W mass picks L over Q (`SharedReference.reference_selected`). Premises: one reserved cell per reference type; both electroweak refreshes read the reserved reference. |
| Strong α_s in (0.11799520370,0.11799520373) | Current formula α·footprint/(12η), exact carrier colour support, conditional colour geometry and refined bounds. | Normalization: charge units, as for the weak sector. Colour's reference lies in the payload, since the reserved cell carries the colourless L reference, and 12η is the Economy-minimal refresh of the coloured payload (`ColourReference.colour_ledger_minimal`). Colour's twelve reads are forced by the record bound (`SectorObligations.colour_needs_twelve_reads`, `colour_cost`). The matching scale is derived: colour's coupling runs at every scale, so an exact read is at the executing mass, the Z (`ReadScale.colour_exact_read`, `OnShell.z_read_scale`). The legacy (16η+1/4)α is not the public current formula. |
| g_W, g_Y, g_3 | All three couplings from Paper II's D₄ gauge action and summed reference read (`GaugeGroupFactor`, `ReferenceStiffness`, `ChainCouplings.chain_couplings` = `couplings_from_alpha`). Also: calibrated formulas, common-stiffness consequences and actual packet actions. | Paper II premises: cubic link consistency across spacings and the readout contract (which states each refresh reads). Physical scale convention. The lepton-doublet reference supplies the readout/work asymmetry (`ReferenceAnchor.lepton_reference_breaks_root`). |
| Scalar λ=128/989 ≈0.1294236603 | `ScalarLedger` factorises `λ = (σ−χ − 1/Δ)/(ν+σ+χ)`, proves `scalarGain_eq`, `scalarTollLedger_eq`, `scalarMassSq_eq`, `scalarBudget_eq_movedCount` (links to `ReferenceDirections.displacement_dim`). Exact budget benchmark and conditional scalar response. `PersistentGain` constructs a largest gain paying its own reflection. | Budget 3 read as the three electroweak directions that move the reference (`ReferenceDirections.budget_is_moved_count`; premise one unit per moved direction). Equal gain is the maximin allocation and N = 23 is pinned once B = 3 (`RegulatoryMaximin`); the 23 labels are the coordinates (channel, wire, boundary) of a link hop (`RegulatoryLabels`); ν+σ+χ is the only decomposition into distinct architecture inputs and finite restoration has trace 3 (`ReferenceRestoration`), clock credit and reflection charge c. For c>0 the persistent optimum is strictly below 128/989; agreement within a bound is not an exact identification. |
| Scalar Toll T=2λ and μ²=λv² | Scalar kinetic normalization `Z_φ = (3/4)·toll·m = 3/(8πα·footprint)` from Paper II's event-priced scalar transport (`ScalarNormalization`). Also: accounting identities under the stated scalar normalization. This Toll is distinct from the inherited substrate toll in Paper I. | Budget dynamics and the substrate amplitude `v_sub`. |
| VEV v | `VevLedger` factorises `v = slotCount · α⁻¹ · (1+α/D_eff) · (1−Y/(σ−χ)) · m_e`; `VevClosure.vev_closure` composes it. Closed: slot arithmetic `3510`, handoff identity under event calibration, divisor `3` via `σ−χ=D−1`, boundary uniqueness `χ/(4π)`, one-repair count. | Remaining are **named inputs**, not VEV arithmetic: (i) channels-as-frame / wires-zero-boundary reading, (ii) physical content of the one repair, (iii) noise-on-reference-orthogonal axes, (iv) the `m_e` mass anchor, (v) physical controller/register implementation. The VEV formula itself is no longer open. |
| Electron Yukawa y_e in (0.00000293502845,0.00000293502847) | Current definition sqrt(2)/(v/m_e) gives exact electron mass closure; `VevDownstream.vev_downstream` records the closure conditional on the VEV ledger. | An independently derived dressing if claimed as a separate prediction. The earlier 5/4-dressed formula is excluded by joint closure and retained only as a regression. |
| Fermi constant G_F | Derived as W exchange on the reference: m_W² = g²v²/4 and Paper II's contact matching give 1/(sqrt(2) v²) (`MatterRunning.fermi_from_reference`). The full V−A four-fermion amplitude is the zero-momentum limit of W exchange (`WeakSpectrumLinks.reference_contact`, Paper II `WeakVertex`). `VevDownstream.vev_downstream` ties the normalization to the composed VEV ledger. | The remaining VEV inputs (named in the VEV row); the four-fermion normalization is the W-exchange contact limit, not independent of the same proposed v. |
| Higgs mass m_H | Canonical curvature 2λv² and conditional mass bounds; `VevDownstream.vev_downstream` records `m_H²=2λv²` against the VEV ledger. Comparison using measured G_F is an external-input test. | Physical scalar normalization, reflection-paying λ, and response corrections. The VEV factor is no longer the blocker; the named VEV inputs remain. |
| W/Z masses | `m_W² = (3/344)v_sub²` and the Z mass in units of `v_sub` from the chain couplings and scalar normalization (`ScalarNormalization.w_mass_geometric`, `z_mass_geometric`, `mass_ratio`). `VevDownstream.w_mass_from_canonical_vev` writes the W mass in terms of the VEV when `vev = canonicalVev`. Tree-level ρ = 1 and the massless photon follow from the doublet reference (`ReferenceMasses.rho_one`, `neutral_form`). | The identification `vev = canonicalVev`/`v_sub` and a derived interface factor Δr. A measured Z mass tests the W relation but does not independently predict both absolute masses. |
| Hypercharges / generation content | Multiplicities 6,3,3,2,1,1; conditional charges from flux, a unit link and neutral sterile channel; `ReferenceLink.standard_or_conjugate` fixes the charges up to the `e`/`ν` labeling convention; three unordered glue-class pairs. | Chirality/triality interpretation (the lepton axis is the reference's axis and colour its stabilizer, `ReferenceAxis.axis_stabilizer`); neutral-channel selection now follows from the link carrying the reference's hypercharge (`ReferenceLink.neutral_from_reference`, `sterile_unique`); and a complete physical generation classification. `GenerationEncoding` exhaustively classifies the three unordered distinct-class pair types, but distinguishes that from a physical generation space: 48 generation-labelled modes cannot inject into the 24 minimal carriers, even by a linear amplitude encoding. One binary tag suffices exactly. `GenerationHistory` stores it in a companion carrier; `GenerationWalls` uses the existing two-wall label with a cyclic incidence convention, without adding a new kind of label. Physical accessibility, the current and the full update still need identification; in that wall convention the bare wall swap is not an independent generation-preserving action. Equal-class packets remain distinguishable if their wall tag is retained, so their exclusion requires a vector-faithful readout contract. Six weak/colour orbits are not six classes protected by every carrier operation, but a persisting reference excludes the lepton–colour roots that cross them (Paper IV `MassTermLaw`). Paper II's `CarrierClassBundle` offers a simpler dynamically realized class-sector alternative with class-independent observed wall parity; `GenerationVacuumChoice` tests it here. It is degenerate before a breaking law and is not identified as physical generations by the encoding. Paper IV's `GenerationLink`/`GenerationBreaking` describe conditional symmetry consequences. |
| Strong CP θ̄ | Conditional exchange-to-Hermitian implication, determinant/phase results and cancellation of one doublet's vacuum phase. | An actual update's exchange symmetry and positivity of masses/determinants. θ=0 is the unique least-cost vacuum on the whole circle given positive weights with the unit winding weighted, for cost read from Re Z (`PersistenceClosures.strict_vafa_witten`; `abs_not_unique` shows |Z| does not decide). Minimal descriptions or identical D4 sectors alone do not prove those conditions. |
| Running coefficients / flavour / J | b₃ = 7, b₂ = 19/6, b_Y = −41/6 from the derived content (`MatterRunning.standard_coefficients`). Every spin term is derived in Paper II: `RunningResponse` gives spin ½ and spin 0, with Zeeman g = 2 from the Clifford relations and the Landau sum; `GaugeFluctuation` gives spin 1, with the Yang–Mills Hessian `−D² + 2[F,·]`. These are linked by `RunningResponseLink` and `RunningDerived`. Asymptotic freedom is the spin-1 `2F` term (`freedom_needs_spin`). Also: conditional running arithmetic and consistency/exclusion tests. Physical flavour mixing belongs with companion dynamics. | Thresholds and derived mixing angles/phases (flavour is Paper IV). Scale matching is derived (`ReadScale`, `OnShell`). One-loop inputs are proved in Paper II: the FP power (`FluctuationClosure`), the continuum integration by parts (`ContinuumFields`) and the Landau degeneracy (`LandauDegeneracy`). The lattice second variation converges to the continuum Hessian (`LatticeToContinuum`). The classical site-sum step is now supplied by Paper II `LatticeSiteAction` (bounded Jordan regions and its smooth-transport assumptions); its native packet instance is conditional on smooth controls and admission of coherent evolution (`NativePacketUpdate`). Those results do not select the physical controls, representation or matter fluctuation/continuum identification. |
| Jarlskog J | Paper IV's matrix value J_CKM ≈ 3.023·10⁻⁵ (`PMFlavor.CKM.pm_jarlskog_matrix`) is the invariant; Paper III's φ²ηT_geo ≈ 3.085·10⁻⁵ differs by ~2% (`PMFlavor.JarlskogReview`) and is kept only as an estimate. | Calculator updated: `JarlskogVal` is now the matrix value, `JarlskogGeoVal` the estimate; χ² regenerated. |
| Gravitational coupling α_G | Conditional attenuation α^(43/2), residual accounting and bounds near 1.7517995·10^−45. | Actual handoff probability p=α, multiplicative layer/loop law, reversal condition and residual 16−2/3−α. Geometric symmetry or a real update alone does not establish all stochastic premises. |
| Planck scale | The unity scale m_e/sqrt(α_G) of the chosen impedance formula. | Physical α_G and its normalization; defining a unity scale is not an independent absolute-scale prediction. |
| Thermal floor / vacuum-density readout | Positive proposed floor, hierarchy and conditional formulas; bare floor around 9.21 meV with the electron mass input. | Physical propagation depth, thermal/mode population, coupling and interpretation of the floor as a density. |
| Neutrino masses / splittings | The stated tower has gap ratios 1:1849:1850; no common multiplier repairs its splitting ratios. | A derived propagation/mixing Hamiltonian or nonuniform response, in Papers V/VI. The bare/common-rescaling identification is excluded; arbitrary alternative dynamics is not. |

## Shared proof dependencies and order

1. **Maintained state, readout controller and primitive repair task.** This is
   the main common blocker for gauge normalization, η as work and parts of the
   scale handoff. Separate prepared probabilities from effective repair weights.
   `ControllerLedger` now packages the finite typed-repair candidates, their cost
   `activeBudget`, and least-cost selection for the baseline, target-mixing, and
   all-equal constraints (costs 15, 21, 43).  `gaugeController` identifies the gauge-active controller with the
   target least-cost repair (cost 21) and proves it reproduces `clockRatio`.
   The remaining input is the final physical controller implementation, not the
   selection rule.
2. **Minimum necessary work and its symmetry.** Price admissible primitive
   words executing that task, including references/controller records. The
   matched integer lengths in `TypedRepairWork` are conditional bounds, not a
   selected implementation. The elementary root inverse itself has minimum one.
3. **Scalar budget, VEV and interface.** These then support λ, y_e (if independent),
   G_F and absolute masses. A dimensionful anchor remains explicit.
4. **Actual update symmetries and propagation.** These support generations,
   strong CP, running, gravity and neutrino/flavour dynamics; some belong in the
   companion papers. They need not wait for every gauge-work detail. Before using
   a three-generation tensor factor in Paper IV, realize its retained pair-type
   distinction. `GenerationEncoding` proves the exact capacity and linear-space
   requirements and gives reversible binary encoding; it does not select a
   physical history, extra factor, or generation-transition law.

The current failure tests narrow routes without excluding all PM dynamics.
Stationary diagonal preparations with nonzero Q-u/Q-d hops miss the proposed
raw mixing. Coherences also fail in the specified pairwise zero-onsite family.
Uniform or paired-reflection-invariant work is not sufficient to recover both
current raw-ledger readouts. Effective-stiffness ledgers, state-dependent protocol
work and more general dynamics remain possibilities that need derivations.

## Current proof entry points

- Formulas/bounds: `CurrentConstants`, `CertifiedConstants`, `StrongLedgerBounds`.
- Controller and required work: `CoherentComparisonRepair`, `ControllerHamiltonian`,
  `TypedRepairWork`.
- Carrier/response classification: `CarrierReadoutOrbits`, `GaugeReadoutWeights`,
  `WeightedReadoutResponse`, `PrimitiveReadoutSymmetry`, `LinkPreparation`.
- Persistence accounting: `General`, `SelectedColourLoad`, `GaugePersistenceChoice`.
- Scalar/scale: `PersistentGain`, `VevAccounting`, `VevPremises`, `ScaleConsistency`.
- Update/propagation obligations: `SectorExchange`, `HermitianMass`, `DepthEvents`,
  `GravityAccounting`, `FloorNeutrino`.

See [`OVERVIEW.md`](OVERVIEW.md) for the module map and [`README.md`](README.md) for
build instructions.

### Controller cost does not derive η

`ControllerIdentification.gaugeController` reproduces `clockRatio`, but its
active budget is `21`, not `171/172`.  The overhead `η=171/172` is the
one-reserved-cell fraction of the 172-cell frame, not a controller repair count.
So the controller ledger does **not** derive η as work; η remains the frame
overhead input.
