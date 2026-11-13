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
| Overhead η=171/172 | Capacity/coding theorems, geometric axis balance, conditional reference-star maintenance and return-law minimization. | Register width/reference factorization reduced (`RegisterWidth`): the reference sits inside the node's forced `D·Δ = 172` registers, and `η` needs a cell alphabet of at least 172 states statically and 173 with the clock running (`GridEncoding.grid_one_slot_iff`); a cell holding one E8 transition (240 roots) clears both and gives `171/172`, a channel-only cell (16) would give `170/172`. Open: what one (axis, phase) cell holds. Readings: one E8 root (240) or a full transition description (`FinalPremises`, 31 bits) clear 173 and give `171/172`; one axis's share of a description (≈31/4 bits) is borderline; a channel label (16) gives `≤ 170/172`. `FinalPremises` describes a transition across all four axes at once, which points to a whole transition per tick column, not per cell. Against the direct m_W average (the same tree formula as e8p `ReadoutPulls.w_mass`) and α_s, summed squared pulls are `1.34` for `171/172`, `1.04` for `170/172` and `4.6` for a register per tick column (`η = 42/43`, `one_register_per_tick_static_optimum`): the column reading is disfavoured (α_s +2.1σ), and Paper III's register model is per cell anyway (one independently settable component per direction and clock phase, Paper I's `R_M = DΔ` addresses per cycle); `171/172` and `170/172` are not separated. Paper III states the width `a ≥ 173` as an operational premise and does not derive it. Data on the width (same two pulls): binary cells (`164/172`, χ² 29.5) and ternary cells (`167/172`, χ² 8.5) are excluded, so a cell is not one bit even though Paper I's observations are one-bit; any `a` from about 14 to 172 gives `170/172` (χ² 1.04), `a ≥ 173` gives `171/172` (χ² 1.34). Paper-native candidates: an E8 root (240, `171/172`); Postulate I's slot content, one of `N = 32` channels or idle (33, `170/172`); a Toll target over all `R_M` addresses or idle (173, `171/172`, exactly the clock threshold, found by looking for 173). Protocol names the successor among the `R_M − σ = 167` residual addresses, which with idle is 168 and gives `170/172`. The other η-dependent outputs separate the two: the quark masses (`QuarkMasses`, ∝ 1/η: m_s, m_c(m_c), m_b(m_b)) give χ² `1.66` vs `11.65` (m_b +3.3σ at `170/172`), and the Cabibbo first-row deficit `(1−η)/D` (`CabibboDressing`, measured sum `0.9984 ± 0.0007`) gives `+0.21σ` vs `−1.87σ`. Over all six, χ² `3.0` (`171/172`) vs `16.2` (`170/172`). Caveat: those formulas were written with `η = 171/172`, so this is consistency, not an independent test; but it favours wide cells, `a ≥ 173`. (Maintenance is required: skipping it under drift fails, `ReferenceAxis.skipped_maintenance_fails`), and an actual preparation/sampling contract. `ContentWeight.economy_selects_intensive` proves a numerical ordering, not physical admissibility or selection. |
| Weak fraction s=1849/8295 ≈0.222905365 | End to end from the derived table (`TableConsequences.end_to_end`). Exact ledger arithmetic, controlled carrier comparison response and explicit weighted response indices. | The operator comparison for involution-phase words now has an exact marker-free circuit (`CarrierPhaseComparison`, Paper II `InvolutionComparison`), and a supplied two-cell spatial register has exact all-state semantics (`SpatialComparison`). Gate/phase admission now has a stated rule (`PMAction.Admission`: unitary, local, priced, admitted by default); which E8 root words realize the gates, clean-cell allocation, preparation/repair work and the clock/spatial/wire requirements remain open (the typed repair lengths that give `clockRatio` are unique at least cost, and `RootRepairRule` gives them from one root event per non-abelian factor, as a candidate). Nine forward phase calls are not a minimum primitive price. Raw uniform packet response gives 5547/37777, so current matching cannot be inferred from one common calibration. With the selected (uniform) preparation the W mass excludes that raw reading by >289σ and keeps the effective one within 1.3σ (`E8PConstants.ReadoutPulls.ledgers_are_effective`): the ledgers are effective stiffness, i.e. charge-unit normalized; the packet trace-form (unified) normalization gives the excluded raw value (`GeneratorNormalization`). A common reference carrier gives that exactly when it is the lepton doublet (`ReferenceCharge.equal_response_iff`); a shared colour-invariant reference is exactly L (`shared_colourless_reference_iff`); sharing follows from the single reserved cell that fixes η, and the W mass picks L over Q (`SharedReference.reference_selected` with the measured `E8PConstants.ReadoutPulls.reference_selected_wmass`). Premises: one reserved cell per reference type; both electroweak refreshes read the reserved reference. |
| Strong α_s in (0.11799520370,0.11799520373) | Current formula α·footprint/(12η), exact carrier colour support, conditional colour geometry and refined bounds. | Normalization: closed (`ColourNormalization`): a colour generator's packet trace is `4×` its fundamental trace, as for weak, so the trace-form and charge-unit rules both give `tr TᵃTᵇ = δ/2`; only hypercharge distinguishes them. Colour's reference lies in the payload, since the reserved cell carries the colourless L reference, and 12η is the Economy-minimal refresh of the coloured payload (`ColourReference.colour_ledger_minimal`). Colour's twelve reads are forced by the record bound (`SectorObligations.colour_needs_twelve_reads`, `colour_cost`). The matching scale is derived: colour's coupling runs at every scale, so an exact read is at the executing mass, the Z (`ReadScale.colour_exact_read`, `OnShell.z_read_scale`). The legacy (16η+1/4)α is not the public current formula. On the hadron carrier cube this coupling does not act unchanged: one-gluon exchange at 0.118 gives an N–Δ splitting of 6 MeV against 293 observed (`tools/colour_fluctuation.py`); the carrier-cube coupling is open (`PMAction/REVIEW-AND-NEXT` A.3). |
| g_W, g_Y, g_3 | All three couplings from Paper II's D₄ gauge action and summed reference read (`GaugeGroupFactor`, `ReferenceStiffness`, `ChainCouplings.chain_couplings` = `couplings_from_alpha`). Also: calibrated formulas, common-stiffness consequences and actual packet actions. | Paper II premises: cubic link consistency across spacings. The readout contract is now derived: the squared readout is `PMAction.ReadoutRule.born`, and the generic event coupling (`refresh_ledger`, `coupling_from_events`) lives in `PMAction.EventCoupling`. Physical scale convention. The lepton-doublet reference supplies the readout/work asymmetry (`ReferenceAnchor.lepton_reference_breaks_root`). |
| Scalar λ=128/989 ≈0.1294236603 | `ScalarLedger` factorises `λ = (σ−χ − 1/Δ)/(ν+σ+χ)`, proves `scalarGain_eq`, `scalarTollLedger_eq`, `scalarMassSq_eq`, `scalarBudget_eq_movedCount` (links to `ReferenceDirections.displacement_dim`). Exact budget benchmark and conditional scalar response. `PersistentGain` constructs a largest gain paying its own reflection. | Budget 3 read as the three electroweak directions that move the reference (`ReferenceDirections.budget_is_moved_count`; premise one unit per moved direction). Equal gain is the maximin allocation and N = 23 is pinned once B = 3 (`RegulatoryMaximin`); the 23 labels are the coordinates (channel, wire, boundary) of a link hop (`RegulatoryLabels`); ν+σ+χ is the only decomposition into distinct architecture inputs and finite restoration has trace 3 (`ReferenceRestoration`). Now closed: `B = 3` is any linear, frame-independent readout of an exact repair (`BudgetReadout.budget_readout`), the `1/Δ` clock credit is the same unit (`ledger_from_readouts`), and the reflection charge is `c = 3` (`ReflectionCharge.charge_rate`), which puts the persistent gain within `1.4·10⁻⁹` below 128/989 (`gain_at_three`). Remaining premises: unit = one restored direction; the clock re-synchronized once per cycle; reflected load restored by the same kind of repair. The gain is below 128/989 by that bound, not equal to it. |
| Scalar Toll T=2λ and μ²=λv² | Scalar kinetic normalization `Z_φ = (3/4)·toll·m = 3/(8πα·footprint)` from Paper II's event-priced scalar transport (`ScalarNormalization`). `ScalarVevLink.vsubOfVev` recovers the substrate amplitude from the VEV once the scalar calibration is supplied. | Budget dynamics; the VEV ledger's named inputs. This Toll is distinct from the inherited substrate toll in Paper I. |
| VEV v | `VevLedger` factorises `v = slotCount · α⁻¹ · (1+α/D_eff) · (1−Y/(σ−χ)) · m_e`; `VevClosure.vev_closure` composes it. Closed: slot arithmetic `3510`, handoff identity under event calibration, divisor `3` via `σ−χ=D−1`, boundary uniqueness `χ/(4π)`, one-repair count. | Earlier "named inputs" are now **derived**: (i) wires carry no boundary weight (`VevPremises.wire_share_excluded`; a 1-cell meets the node boundary in points), (ii) the linear form is one exact repair (`VevReadout.exact_net_is_identity` + `PersistenceClosures.one_repair`), (iii) the noise divisor is a normalized spatial-axis readout (`VevReadout.normalized_share`/`time_weight`). Remaining: only the `m_e` mass anchor (external unit) and the physical controller/register implementation. |
| Electron Yukawa y_e in (0.00000293502845,0.00000293502847) | Current definition sqrt(2)/(v/m_e) gives exact electron mass closure; `VevDownstream.vev_downstream` records the closure conditional on the VEV ledger. | An independently derived dressing if claimed as a separate prediction. The earlier 5/4-dressed formula is excluded by joint closure and retained only as a regression. |
| Fermi constant G_F | Derived as W exchange on the reference: m_W² = g²v²/4 and Paper II's contact matching give 1/(sqrt(2) v²) (`MatterRunning.fermi_from_reference`). The full V−A four-fermion amplitude is the zero-momentum limit of W exchange (`WeakSpectrumLinks.reference_contact`, Paper II `WeakVertex`). `VevDownstream.vev_downstream` ties the normalization to the composed VEV ledger. | The remaining VEV inputs (named in the VEV row); the four-fermion normalization is the W-exchange contact limit, not independent of the same proposed v. |
| Higgs mass m_H | Canonical curvature 2λv² and conditional mass bounds; `VevDownstream.vev_downstream` records `m_H²=2λv²` against the VEV ledger. Comparison using measured G_F is an external-input test. | Physical scalar normalization and response corrections (the reflection-paying λ is within `1.4·10⁻⁹` of 128/989, `ReflectionCharge.gain_at_three`). The VEV factor is no longer the blocker; the named VEV inputs remain. |
| W/Z masses | `m_W² = (3/344)v_sub²` and the Z mass in units of `v_sub` from the chain couplings and scalar normalization (`ScalarNormalization.w_mass_geometric`, `z_mass_geometric`, `mass_ratio`). `ScalarVevLink.w_mass_from_vev`/`z_mass_from_vev` eliminate `v_sub` in favour of the VEV and the calibrated `Z_φ`. `InterfaceCorrection` names `Δr = 1−1/k`, proves its Z-anchor window and its decomposition `Δr = Δα − X`, with the leading top-splitting term and remainder bounds. Tree-level ρ = 1 and the massless photon follow from the doublet reference (`ReferenceMasses.rho_one`, `neutral_form`). | The comparison inputs `Δα`, top mass and the non-leading remainder `R`; plus the VEV ledger's named inputs. A measured Z mass tests the W relation but does not independently predict both absolute masses. |
| Hypercharges / generation content | Multiplicities 6,3,3,2,1,1; conditional charges from flux, a unit link and neutral sterile channel; `ReferenceLink.standard_or_conjugate` fixes the charges up to the `e`/`ν` labeling convention; three unordered glue-class pairs. | Chirality/triality interpretation (the lepton axis is the reference's axis and colour its stabilizer, `ReferenceAxis.axis_stabilizer`); neutral-channel selection now follows from the link carrying the reference's hypercharge (`ReferenceLink.neutral_from_reference`, `sterile_unique`); and a complete physical generation classification. `GenerationEncoding` exhaustively classifies the three unordered distinct-class pair types, but distinguishes that from a physical generation space: 48 generation-labelled modes cannot inject into the 24 minimal carriers, even by a linear amplitude encoding. One binary tag suffices exactly. `GenerationHistory` stores it in a companion carrier; `GenerationWalls` uses the existing two-wall label with a cyclic incidence convention, without adding a new kind of label. Physical accessibility, the current and the full update still need identification; in that wall convention the bare wall swap is not an independent generation-preserving action. Equal-class packets remain distinguishable if their wall tag is retained, so their exclusion requires a vector-faithful readout contract. Six weak/colour orbits are not six classes protected by every carrier operation, but a persisting reference excludes the lepton–colour roots that cross them (Paper IV `MassTermLaw`). Paper II's `CarrierClassBundle` offers a simpler dynamically realized class-sector alternative with class-independent observed wall parity; `GenerationVacuumChoice` tests it here. It is degenerate before a breaking law and is not identified as physical generations by the encoding. Paper IV's `GenerationLink`/`GenerationBreaking` describe conditional symmetry consequences. Admission no longer distinguishes the classes: `PMAction.ClassAdmission.all_classes_admitted`. |
| Strong CP θ̄ | θ̄ = 0 for any invertible quark masses (`ThetaBarSelection`): the vacuum phase is selected by least cost and the winding weights see only θ̄ = θ − arg det M. Both cost readings pick it (`PersistenceClosures.strict_vafa_witten` for Re Z, `VacuumModulus.strict_modulus` for ‖Z‖). `WindingWeights` derives w₀, w₁ > 0 from persistence (exp(−βS) > 0 on every history, Haar charges open sets) on Lüscher's non-exceptional fields (`theta_zero_admissible`). The Hermitian-mass route (`HermitianMass`, `SectorExchange`, `WallParityExchange`) is no longer needed for θ̄. | Imported or cited, not formalised: the chiral-anomaly relation (index theorem; the walls' chiral zero modes, `WallSeesaw`, are where it lives), Lüscher's lattice charge on PM's region (boundary pure gauge in the persisting vacuum), and a charge-1 non-exceptional history (every sector nonempty on a large enough region). Premise: the vacuum phase is a variable the selection acts on (in the Standard Model this is the axion's job). |
| Running coefficients / flavour / J | b₃ = 7, b₂ = 19/6, b_Y = −41/6 from the derived content (`MatterRunning.standard_coefficients`). Every spin term is derived in Paper II: `RunningResponse` gives spin ½ and spin 0, with Zeeman g = 2 from the Clifford relations and the Landau sum; `GaugeFluctuation` gives spin 1, with the Yang–Mills Hessian `−D² + 2[F,·]`. These are linked by `RunningResponseLink` and `RunningDerived`. Asymptotic freedom is the spin-1 `2F` term (`freedom_needs_spin`). Also: conditional running arithmetic and consistency/exclusion tests. Physical flavour mixing belongs with companion dynamics. | Thresholds and derived mixing angles/phases (flavour is Paper IV). Scale matching is derived (`ReadScale`, `OnShell`). One-loop inputs are proved in Paper II: the FP power (`FluctuationClosure`), the continuum integration by parts (`ContinuumFields`) and the Landau degeneracy (`LandauDegeneracy`). The lattice second variation converges to the continuum Hessian (`LatticeToContinuum`). The classical site-sum step is now supplied by Paper II `LatticeSiteAction` (bounded Jordan regions and its smooth-transport assumptions); its native packet instance is conditional on smooth controls and admission of coherent evolution (`NativePacketUpdate`; under `PMAction.Admission`'s rule that admission holds: `native_conserving`, `native_local`). Those results do not select the physical controls, representation or matter fluctuation/continuum identification. |
| Jarlskog J | Paper IV's matrix value J_CKM ≈ 3.023·10⁻⁵ (`PMFlavor.CKM.pm_jarlskog_matrix`) is the invariant; Paper III's φ²ηT_geo ≈ 3.085·10⁻⁵ differs by ~2% (`PMFlavor.JarlskogReview`) and is kept only as an estimate. | Nothing for the value (the calculator uses the matrix value `JarlskogVal`; `JarlskogGeoVal` is the estimate). The CKM angles and phase it depends on are Paper IV's (`PMFlavor`). |
| Gravitational coupling α_G | Conditional attenuation α^(43/2), residual accounting and bounds near 1.7517995·10^−45. | The layer/hop law (`DepthEvents.required_handoffs`), the half-depth `α^{43/2}` from the closed `α^43` loop under time reversal (`one_way_from_loop`), and the residual `B_res = ν − χ/(σ−χ) − α` (E8 + α) are **derived**. The identification handoff probability = `α` is reduced (`HandoffAdmittance`): `α` is PM's admittance `1/Z_geo`, and with transmission linear in admittance and a unit channel open (the Ohmic/Landauer reading `ProtocolToll` already uses) the handoff probability is `α`. Remaining: that a gravitational handoff is a channel of that kind, and the closed-loop realization. |
| Planck scale | The unity scale m_e/sqrt(α_G) of the chosen impedance formula. | Physical α_G and its normalization; defining a unity scale is not an independent absolute-scale prediction. |
| Thermal floor / vacuum-density readout | Positive proposed floor, hierarchy and conditional formulas; bare floor around 9.21 meV with the electron mass input. | Physical propagation depth, thermal/mode population, coupling and interpretation of the floor as a density. |
| Neutrino masses / splittings | The stated tower has gap ratios 1:1849:1850; no common multiplier repairs its splitting ratios. | A derived propagation/mixing Hamiltonian or nonuniform response, in Papers V/VI. The bare/common-rescaling identification is excluded; arbitrary alternative dynamics is not. |

## Selection symmetry — the shape of the open choices

The strongest open choices here reduce to one framework fact
(`PersistenceMechanics.SelectionSymmetry`): a cost can only select its fixed points
(`unique_minimizer_fixed`), so a moved point is tied (`exists_tied_of_moved`).
`exchange_fixed_of_unique` applies it: the **Hermitian link mass** premise "the update
carries no sector label" is reduced to invariant-cost + unique-minimizer, and
`exchange_hermitian` then gives `M = M†`. This is a **discrete** symmetry, so it
resolves the choice when the cost forces uniqueness. It fails for continuous tie families
(`ReferenceSelection.invariant_cost_tie` + `different_link` tie two distinct links).

**Strong CP no longer depends on it.** `ThetaBarSelection`: the vacuum phase is what
persistence selects, and with the chiral-anomaly premise the winding weights see only
`θ̄ = θ − arg det M`, so the least-cost vacuum has `θ̄ = 0` for any invertible masses. Both cost
readings agree (`Re Z`: `strict_vafa_witten`; `‖Z‖`: `VacuumModulus.strict_modulus`).
`WindingWeights` derives the needed `w₀, w₁ > 0` from persistence on Lüscher's non-exceptional
fields. Open inputs: the anomaly relation (index theorem, imported), Lüscher's construction on
PM's region, a charge-1 history (both cited), and whether a cost reading other than these two is
admissible.

## Cross-link audit (Nov 2026)

Premises stated here that another part of the library already settles or changes:

* **Common toll.** "Pricing by the common readout event" (`ChainCouplings`, `GaugeGroupFactor`,
  `ReferenceStiffness`, `ScalarNormalization`, `EventStiffness`): the common toll is PM's cost
  definition, one toll `c₀` per transition (`PMSubstrate.NetCost`). The open part is the repair
  length `m`. It is **not** common across carrier types: `TypedRepairWork.common_repair_cannot_match`
  (a common length misses E8's `clockRatio`; uniform gives `5547/37777`). The least-cost typed
  repair that gives `clockRatio` is unique, `(Q,u,d,L,e) = (2,1,1,1,1)` (`target_budget_unique`).
  `RootRepairRule` (candidate) produces it from representation content: one root event per
  non-abelian factor, at least one per gauge-active carrier (each root lies in one simple factor;
  the hypercharge phase adds no event). Found post hoc, so it explains the selection rather than
  predicting. Whether the gauge, scalar and fermion sectors share `m` stays open.
* **Squared-amplitude readout.** Derived (`PMAction.ReadoutRule.born`); `CommonResponse` still
  listed it as an input (fixed).
* **Admission.** `PMAction.Admission` admits by default, which rules out a hard plaquette
  cutoff as admissibility for the lattice charge (`WindingWeights` uses Lüscher's
  non-exceptional fields instead). Machine REVIEW updated: the admission rule is stated; the
  root-generator evolution is admitted (`NativePacketUpdate.native_local`).
* **Strong CP.** `HermitianMass`, `SectorExchange`, `WallParityExchange`, `PersistenceClosures`
  docstrings now point to `ThetaBarSelection`. The walls' chiral zero modes (`WallSeesaw`) are
  where the imported anomaly premise lives.
* **Preparation.** `PreparationSelection`'s remaining input (identifying the carrier preparation
  with the survival model) matches Machine's "prepared initial reference" input
  (`PrimitiveRecordBoundary.cannot_prepare`): one input, stated in two places.

## Interface correction — closed

`InterfaceResponseLaw.substrate_deltaR_in_window`: the E8 carrier/spectral response
(exact linear repair + the five geometric modes + maximin uniform weight) gives
`K_sub = 1 + σα`, so `Δr_sub = 1 − 1/K_sub = 5α/(1+5α)`, inside the Z-anchor window
`0.0349 < Δr < 0.0353`. The naive isotropic root sum `24/(q²+2)` is excluded
(`InterfaceSpectralCandidate.simple_root_sum_excluded`). The `Δα`/top-mass/remainder
numbers are comparison diagnostics only, not derivation inputs.

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
   Done in PMAction: one clock tick costs `2·toll·m` (`ClockLedger.clock_tick_cost`), and
   admission is unitary plus local (`Admission.Admitted`).
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
