# PMFlavor — overview of checked results

*Persistence Mechanics of the Quantum Vacuum IV: Information Transfer.*

This is the single overview of what Paper IV proves and how it hands off to the
later libraries. Library order: PMSubstrate → PMAction → PMConstants → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`). The actionable open work is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md);
build/layout instructions are in [`README.md`](README.md). The Lean source is the
ground truth; theorem names below are entry points, not an exhaustive list.

## Scope

Paper IV builds on the Paper I substrate (E8, clock Δ = 43, invariants D = 4, ν = 16, σ = 5, χ = 2)
and the Paper II wire (PMAction: the two-wall operator, its label states and light-mass form). Flavour
here is the label state; a flavour change is a label change during a charged-current event. PMFlavor
finds `J`, the label-change amplitudes of one event, for carriers off and on the reference axis (read
out as the CKM and PMNS), and why a transfer persists (transfer selection and work). The observed
matrices are `U_uᴴ J U_d`, with `U` from the wire and the protocols. Comparisons with measurement are
in `tools/e8p/E8PConstants/PMFlavor`. What flavour is here and the terms: [README](README.md). Older
sections below say "generation" for a label state.

## The label changes of one event

**`J` (`EventTransfer`).** On the reference's wall an event changes label `g` to `g − 1` with a carrier
of class `g + 1` (`PMAction.GenerationCurrent`). `J κ` has amplitude `1` for no change and `κ c` for the
change through class `c`, from label `c − 1` to `c + 1` (`entry_of_class`); these are the three
transfers of `TransferGraph` (`entry_is_transfer`). One event makes no reverse change (`reverse_zero`).
The change through class `0` (`2 → 1`) uses the weak carrier itself and stays in the cycle
(`weak_carrier_entry`); the changes through `1` and `2` need a spinor carrier from the node
(`node_entries`). The actual weak refresh (`CarrierActions.weak`) moves only vector-class
carriers of the reference's sector (`refresh_moves_reference`, `refresh_fixes_other`): it supplies
the in-cycle change and no spinor carrier. Completion: `A = N − Nᴴ` (`N` the off-diagonal part of `J`)
is skew-Hermitian (`A_skew`), carries `κ c` forward and `−κ̄ c` in reverse (`forward_entry`,
`reverse_entry`), and `1 + A` is unitary to second order (`first_order_unitary`).

**Three transfers, three types (`TransferGraph`).** Each pair of label states transfers through the
one class both contain (`ends`, `every_pair`). Exactly the transfer through the reference's class
stays inside the maintenance cycle (`inCycle_iff`, from `ExchangeAxis.vector_free`, `spinor_ne`); the
other two cross the reference node by two legs each, and their classes sit on opposite walls of label
state `0` (`node_walls_opposite`, `swap_flips_wall`). A current coupled to one wall separates all
three (`three_types`); a wall-symmetric probe sees two (`two_types_blind`). So the three transfer
types rest on the charged current's one-wall coupling. Mode assignment (candidate, `mode`):
conduction for the in-cycle transfer (derived: the continuous mode is exactly the in-cycle transfer,
`mode_continuous_iff`), promotion for the node crossing on the reference's wall, jump for the other.
The names conduction, promotion and jump are a candidate reading. Placing the label states on a
three-step ladder showed they rest on one premise: the crossing on the reference's wall is one step
and the other-wall crossing two (checked over all maps of the three label states; that module was
removed with the paper-draft tier reading).

**Node-crossing amplitudes (`TransferAmplitude`).** The jump is the two-leg series path,
`1/(2α⁻¹ + π) = s₁₃` (`jump_eq_s13`). The library's rules for the promotion give
`promotion/jump = 1` (one series rule), `≈ 1.98` (one leg from the node), `≈ 23.7` (one leg as a
probability) (`promoA_ratio`, `promoB_ratio`, `promoC_ratio_sq`). Negative result: all three are
excluded by the measured `|V_cb|/|V_ub|` (`E8PConstants.CandidateTests.promo_rules_excluded`); the wall
must change the amplitude by a factor near `10` that no derived rule produces.

**In-cycle rule (`ConductionRule`).** The half-turn share `π/N` (`HalfTurnAperture`, candidate) over
the type-preserving channels: `N = 14` off the reference axis, `10` on it. With the node crossings'
readout (off axis two legs, amplitude; on axis one leg, probability) and no further function, the
in-cycle transfer gives amplitude `π/14 = s₁₂` off the axis (`offAxis_rule`, `offAxis_is_s12`) and
probability `π/10` on it (`onAxis_rule`). The supplied on-axis value `1/(2φ) = sin(π/10)` applies a
sine the off-axis value does not (`sine_reading_differs`).

**Formulas e8p prints.** `CKM.lean`: `s₁₂ = π/14`, `s₁₃ = 1/(χα⁻¹ + π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`,
`δ = arctan(σ/χ)`; `PMNS.lean`: `sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1 + π/(ν+σ))/χ`, `sin²θ₁₃ = (σ−χ)/α⁻¹`,
`δ_PMNS` from the sum rule (`ReferenceFlavour`). Which of these are derived from the transfers is the
status table in REVIEW. `FlavourInvariants` restates them in derived invariants; `GoldenGeometry` and
`SixHundredCell` give `φ` from a pentagon (no transfer mechanism). `α⁻¹` is `PMSubstrate.geometricIndex`.

**Retired and moved (git history).** Removed: the path/cycle operators (`PathOperator`,
`HierarchicalPathOperator`, `PMNSMassOperator`, `CapacityImpedance`), the eigenvector-link picture
(`BreakingLink`, `BreakingPhase`, `MixingMatrix`, `LinkHierarchy`), the whole-matrix typing of
`TransferFlavor`, the oscillation/propagation readout (`Oscillation*`, `CPAsymmetry`, `CPObservables`,
`Propagation*`, `NativeFlavourObservables`, `SymmetricMass`), and the modules that picked integers by
fit (`MixingTests`, `NodePassage`). Moved to PMAction (the wire): the label-state chain, the light-mass
form (`CyclicSeesaw` … `UndetunedWall`, `MassInsertion`, `InterWallDiagonal`, `GenerationLabel`), the
multi-flavour wall operator (`FlavourWallReduction`, `NativeFlavourWall`, `WallSpectrumLink`,
`WallLatticeSpectrum`, `RelativisticPhase`) and `FlavourEvolution`. Library order changed to
PMElementaryParticles → PMFlavor: `DoubletReflection` moved to PMElementaryParticles,
`persistent_single_frequency` to `PMConstants.OnShell`, the PMNS instance of the inclusive width to
`InclusiveWidth`, and `CarrierAmplitude` no longer carries `V_ud`.

## What is checked

**Canonical values.** `PMFlavor.Values` is the single import for downstream libraries
(mirroring `PMSubstrate.E8Values` and `PMConstants.Values`): `vud = c₁₂c₁₃`, `vus = s₁₂c₁₃`,
`vub`, `vcb`, `q2 = 515/516`, `vudDressed`, the angle bounds, Pythagorean identities and
`vus_div_vud = s₁₂/c₁₂`.

**Matrices and mixing.** `CKM`, `PMNS`: complete complex matrices with exact
unitarity, determinant 1, the Jarlskog quartet, and certified squared-entry /
Jarlskog intervals (`PMNSIntervals`: `−0.0217 < J < −0.0215`). The PMNS phase is
fixed by the persistence sum rule `|U_μ2| = |U_τ2|` (`ReferenceFlavour`), on the
`sin δ < 0` branch. Unitarity triangles have area `|J|/2`
(`UnitarityTriangle.area_is_half_J`), with `68.16° < γ < 68.17°`.

**Wall spectrum and native carriers.** `WallSpectrumLink` identifies branch
energies with the relativistic energy law and the light/heavy seesaw;
`FlavourWallReduction` gives the exact multi-flavour reduction; `NativeFlavour*`,
`NativeMassBasis`, `LightFlavourPreparation` realise prepared eigenmodes on the
native carrier and reproduce exact flavour evolution and probabilities.

**Reference persistence.** `ReferenceSpectrum`: persistence iff a single-energy
eigenspace. `SpectralVariance`, `FlavourStationarity`: residual coordinates and
gap bounds. `persistent_single_frequency`: a persisting state is one energy/
frequency, hence on-shell (now `PMConstants.OnShell.persistent_single_frequency`, shared with
PMElementaryParticles).

**Selection and restoration.** `AllRootRestoration`, `RootRepairSelection`,
`RestorationBudget`: the six-reflection restoring alphabet, unique cheapest word,
minimum density. The five selection tests (`ReferenceSelection`,
`NativeReferenceFreedom`, `FlavourResponseSelection`, `SelectionSymmetry`,
`TransitionSelection`) isolate what a persistence cost can and cannot select.

**Lepton axis, Dirac survival.** `LeptonAxisRestriction` (per-cycle contract) plus
`MassTermLaw` give `dirac_survival`: only the Dirac neutrino mass term survives;
active-Majorana and sterile terms are unreachable. `PerStepContract` strengthens
this to per-step maintenance: `perStep_root_axis_zero` derives the restriction
from a single restored step, `run_roots_axis_zero` gives it for every event in a
restored run, and `sampleEvent_pair_not_maintained` closes the paired-event
(involution) bypass that a cycle-end-only check would admit.

**Transfer cost and generation selection.** `RelativeFrameCost` prices a frame by
`‖AB−BA‖²/12 = Σ gap·weight/12`. `TransferWorkLaw` shows the least-work route is
the smallest-gap pair; `SpectralGapOrder` derives the gap ordering from the
spectrum (`gap = 2 − 2cos|t·Δe|`); `ChordBranch` reduces the one-branch hypothesis
to `t ≤ tStar` and discharges it at `tStar`; `TransferAmount` shows any positive
transfer costs positive work.

**The link, derived.** `SubstrateLink.linkOverlap` is the glue-class overlap
matrix (`2` diagonal, `1` off), `S₃`-invariant with spectrum `{4,1,1}`: a degenerate light doublet.

**The network on the incidence.** `LinkKronComparison`: the generation–class incidence (each class
vertex has two legs) has the glue-class overlap as its Gram matrix `B Bᵀ` (`linkOverlap_eq_gram`),
and its conserving network reduces by Kron elimination of the class vertices (`kron_schur`) to two
legs in series, which is where the `2` of `|V_ub| = 1/(2α⁻¹ + π)` comes from
(`two_leg_from_incidence`; one shared node with three legs would give `3`, `shared_node_three_legs`). The eigenvector-link picture of mixing (a broken
`linkOverlap` whose eigenvectors are the mixing) was retired: it fixes one mixing entry at
`|U|² = 1/4` for every breaking and, through `WallSeesaw`, cannot carry a charged-lepton hierarchy.
Its modules were removed (git history).

**Where a CP phase can sit.** `LinkFlux`: with complex legs the reduced coupling through a class is
`−t₁ t̄₂/(g₁ + g₂)`, class phases cancel, and each sector keeps one invariant, the flux of the
reduced triangle. A wall-side leg phase gives flux `ū⁶` (`flux_cyclic`); exchanging the wall names
conjugates it (`flux_swapped`); the `μ`–`τ` swap reverses the incidence orientation
(`swap_reverses_orientation`), so CP violation needs that `Z₂` broken by the wall assignment, and
its sign is the wall-naming convention. Its size is not fixed. `kronLink_zero_mode`: a real
conserving network shares `(1, 1, 1)` between sectors. `ThirdGenerationMixing`: with a
flavour-blind on-site mass the eigenvectors of `Y` are exact, so two real conserving sectors give
third row and column `(1, 0, 0)` (`zero_mode_unmixed`), the data's leading order (a conserving down
link against a diagonal up basis would give a democratic `1/√3` column instead). `|V_ub|` and
`|V_cb|` are then first-order effects of what lifts the zero mode, divided by the gaps
`3α/2` and `a + α/2` (`in_cycle_spectrum`), so `VubSeriesPath`'s amplitude is not an eigenvector
overlap of the conserving network itself.

**Real legs are excluded in either reading of the mixing** (numerical, outside Lean). If instead the
masses are generation-diagonal and the CKM is the charged current's transfer `V = e^{−iK}` through
the network (`GenerationLabel`'s single-wall hop read as a transfer; not the library's
`WallSeesaw` reading), then with real `K` the second-order term `−½K₁₂K₂₃` adds to `−iK₁₃` in
quadrature, so `|V_ub| ≳ |V_us||V_cb|/2` (exact minimum at the PDG `|V_us|, |V_cb|`: `0.00477`,
against `0.00373`; the PDG ratio `|V_ub|/(|V_us||V_cb|)` is `0.40`). The same holds for any
`1 − iK − K²/2 + …` (Cayley included). So in both readings a real conserving network fails the
third generation, and a flux (or leak) is required. Fitting the PDG
2024 Wolfenstein values with a fluxed generator gives a flux of `43°`–`49°` (statistical `±1°`;
the spread is the choice of generator form and diagonal, so no sharper value is a data statement)
and `|K₁₃| = 0.0043`–`0.0047`, above `VubSeriesPath`'s `1/(2α⁻¹ + π) = 0.0036`, which matches
`|V_ub|` itself rather than the coupling.

**A conserving mass link fails for quarks** (numerical). Both sectors as fluxed incidence links
(three moduli and a flux each; the overall scale drops out), masses from the seesaw, CKM as
`U_uᴴ U_d`: 8 constraints (four mass ratios at `M_Z`, four CKM invariants) on 6 parameters. Best
`χ² ≈ 1040`, from `m_s/m_d` (the fit reaches about `4`, against `20`) together with the CKM; up
masses and the CKM alone fit. With the exact one-flavour mass and a free `δ₀` per sector (8
parameters) it is unchanged (`χ² ≈ 1039`). So mixing as the mismatch of two conserving incidence
mass links (diagonal = sum of the couplings) is excluded for quarks. A mass link with independent
diagonal entries is not excluded, but it has no test until those entries are derived. The transfer
reading (masses generation-diagonal, `GenerationLabel`; the charged current's own single-wall shift)
is the one with a test, and it needs the flux above. `PMAction.WallHopPhase`: an in-wall hop on one
chirality is a quarter turn that cancels in every reduced coupling, so that flux does not come from
the in-wall kinetic hop.

**The gluing forbids a generation-diagonal crossing.** `InterWallDiagonal`: E₈ pairs equal classes
across the walls, so the inter-wall term keeps the class, and an equal-class crossing always
changes the generation (`crossing_changes_generation`): `Y_gap` has zero generation diagonal. If
`Y_gap` is Hermitian (wall-parity exchange symmetry, `WallExchange`), its eigenvalues sum to zero, two
of its singular values are within a factor `2` (`traceless_close_pair`), and under `WallSeesaw` two
light masses are too (`seesaw_close_pair`); every charged sector has its closest pair more than `16`
apart (`no_measured_lepton_traceless`). The crossing itself is directional (a weighted cyclic shift,
whose singular values are the three class amplitudes), so without that symmetry the argument does
not apply. Within one convention the symmetry is broken (`PMAction.GenerationParity`). The
seesaw on that link (`CyclicSeesaw`): `Yᴴ Y` is diagonal (`gram_cyc`), so one Dirac pair per class
with mass `δ²/|y_h|`, pairing generation `h` on one wall with `h + 1` on the other; the crossing is
`DomainWall`'s one hop, the same for every class, so the three seesaw masses are equal
(`gram_equal`). The hierarchy must come from the composite diagonal term
(`PMAction.GenerationMass`). `det Y = y₀y₁y₂` (`det_cyc`), real for real amplitudes
(`light_det_real`). That matters only to the older Hermitian-mass route to `θ̄ = 0`; the current
route (`PMConstants.ThetaBarSelection`) holds for any invertible mass.

**Where the composite enters.** `CompositeMass`: with generation-structured on-site chirality flips
`D₁`, `D₂` the light mass is `M = D₂ Y⁻¹ D₁ᴴ` (`effective_mass_general`). `Y⁻¹` is the reverse shift
(`inv_cyc`), and a carrier with the crossing's support on either side of it is diagonal
(`cyc_mul_cycInv`, `cycInv_mul_cyc`). So with `D = δ + carrier`,
`M = δ² Y⁻¹ + δ · diag(κ/y) + δ · diag(κ'/y) + (second order, cyclic)` (`composite_expansion`): the
composite is a correction to `δ`, linear in the carrier amplitude, so the largest carrier amplitude
is the heaviest generation. The carrier is a chirality flip on its wall through the Wilson part of its
hop (`PMAction.CarrierFlip`, `κ = −r t/2`), given that the class carrier is an in-wall Wilson hop.

**The light split needs two wall asymmetries.** `LightSplit`: with on-site flips `δ_F`, `δ_T` and
carriers on both walls, generation `g`'s composite entry is `δ_T κ_F(e g) + δ_F κ_T(e g)` (one term
per order of `GenerationMass`; `composite_expansion2`). If the carriers keep the class-swap ×
wall-exchange symmetry of `ExchangeChirality`, the light pair's difference is
`(δ_T − δ_F)(κ_F(s) − κ_T(s))` (`light_split`), zero unless both the on-site flip and the carrier
differ between the walls (`split_needs_both`). With one `δ` for both walls, as in `WallSeesaw`, the
pair stays degenerate at this order. Size: a light ratio `R` forces `u + x ≤ 2/R`
(`near_maximal`, `x = δ_F/δ_T`, `u = κ_T/κ_F`), so a large light ratio needs both asymmetries near
maximal, which a perturbative source cannot give.

**No detuning on the reference's wall.** `PMAction.ReferenceDetuning.stationary_iff`: the reference
background is a stationary zero mode exactly when its wall's on-site detuning vanishes. That wall is
the `D₂` slot, so `δ_F = 0`, and `ReferenceWallMass.reference_wall_mass` factors the light mass as
`M = D_R (δ_O + cyc κ_O)`, `D_R = diag(κ_R/y)`: the hierarchy is the reference-wall carriers of each
generation's label class, the other factor rotates. The seesaw term `δ_F δ_T Y⁻¹` is gone.
Node passage acts on both walls (`LeptonAxisRestriction.cycle_root_axis_zero` constrains the event
root, which acts on both sectors). With the swap × exchange symmetry the light ratio is
`κ_R(s)/κ_O(s)`.

**The node amplitude.** `NodeAmplitude`: the vector carrier is an in-cycle event, which passes
with certainty, so `K = 1` (`HandoffAdmittance.transmission_of_linear`); the spinor carrier crosses
the node by two legs of admittance `α`, which Kron reduction puts in series (`PMAction.KronReduction.kron_two`),
so `k = α/2` (`node_series`, `node_kron`, `node_amplitude_value`: `1/(2Z)`). The mass carrier has no
lead boundary; the CKM transfer adds the `1/π` boundary (`KronSeries.vub_from_kron`).

**The other wall must be detuned.** `UndetunedWall`: at `δ_O = 0` the light mass `D_R cyc κ_O` is a
cyclic shift with entries `a_{h+1} c_h` (`diag_cyc`, `undetuned_gram`), which with the symmetry are
`(kK, k², kK)` (`undetuned_masses`): two heavy, one light, the reverse of every charged sector.

**The wire's charged-current couplings.** The two `K_cc` edges at the label-`v` generation are both
spinor-class through the node (`PMConstants.GenerationWeak`), with one leg weight and the `s ↔ c`
swap, so `K₁₃ = K₂₃`.

**Species masses are protocol work.** The wire above (`ReferenceWallMass`) fixes the form of the
light mass and is blind to the species it carries (`PMConstants.HandoffAdmittance.closure_one_price`,
`PMElementaryParticles.DoubletReflection`). Species are protocols over it
([PMElementaryParticles](../PMElementaryParticles/OVERVIEW.md), "Species masses over the wire").

**What a diagonal mass needs.** `MassInsertion`: a two-wall bilinear has class gap `b + c`
(`bilinear_gap`), so a generation's own mass needs an insertion of its label class. Only the
generation labelled by the reference's class `v` has a vector-class insertion, which can stay
in-cycle (`label_is_reference_iff`); and it is the only generation whose two mixings both cross the
node (`label_v_mixings_cross`, `other_has_in_cycle`). So one fact fixes both patterns. The data choose the direction: if
the insertion enters the mass directly, that generation is the heavy, weakly mixed one
(`|V_ub|, |V_cb| ≪ |V_us|`, as observed). If it enters `Y` and is read through `δ²/σ(Y)`, it is the
lightest, and `|V_us|` would be node-suppressed while `|V_cb|` is in-cycle, the reverse of the data.
So the diagonal mass is an in-wall (on-site) chirality flip, or `WallSeesaw`'s `δ²/σ(Y)` does not
apply to it. For a Hermitian `Y_gap` the on-site version reduced through the seesaw also fails:
`D Y⁻¹ D` leaves the light pair degenerate at leading order (exact block identities
`light_block_inverse`, `light_pair_degenerate`; the leading-order reading is prose; a random scan
stayed below `1.52`, which is a sample, not a bound). For the directional crossing it does not
(sampled ratios up to `10⁶`). So, for a Hermitian `Y_gap`, the light masses do not come from
inverting the link. What survives is
a term joining the two chiral zero modes directly and carrying the label class, which makes the
mass matrix generation-diagonal: the transfer reading's premise, reached from the mass side. Not
yet derived: the wall Hamiltonian has no such term, and the equal-class crossing would add
off-diagonal mass entries unless absent or small.

**Where in the tick does not matter.** `TickPlacement`: with time on axis `0` (the premise of
`DressingInheritance`), vector carriers are equal-time moves or pure ticks and spinor carriers sit at
half ticks, but an insertion's light-mode element is the same wherever in the tick it sits
(`placement_invisible`), and the weak refresh has no special tick. So the class dependence of the
diagonal masses is the node passage already in the library (spinor insertions touch the reference
axis), not a class-dependent Wilson parameter. The node's own odd-sector phase
(`PMAction.Machine.OddCarrierPhase`, continuous in time) gives no CP flux: it is the same in both
directions and enters the zero-energy reduction as a real denominator (`node_denominator_real`).
The remaining sources for the CKM flux are leg phases that differ at a class vertex, or a holonomy
around the generation–class loop. `PMAction.FlatPersistence` prices a holonomy `e^{iΦ}` by
`sin²(Φ/2)` per readout and is minimized by `Φ = 0`, so without a source persistence picks a real
(flat) network; the library has no source for a flux, and the cyclic wall orientation is the only
CP-odd candidate. A six-vertex form (separate up and down generation vertices) models a different
object: the charged current is
generation-universal with isospin a separate factor (`FlavourCurrent`), so the transfer is the
three-lead network of `TransferGenerator`, with one loop. Searched for a source on that loop: none
in the library (no `Z₃` phase anywhere; `CommonResponse` compares with the untransported reference,
so every readout prefers offset `0`). The library therefore has no mechanism for the CKM phase;
the supplied `δ = arctan(σ/χ)` stands without one. The clock cycle does not supply one either: weak is
the sign exchange on vector carriers (`CarrierActions.weak`), which keeps every class, so it never
permutes generations, and its phases are `±1`.

**The transfer is the Cayley form.** `TransferGenerator`: zero-energy scattering through a
Hermitian network with equal leads `γ` (Landauer, `HandoffAdmittance`; zero energy, `KronSeries`;
one price, Closure) is `1 − 2iγ(−K + iγ)⁻¹`, eigenvalue by eigenvalue `−(1 − ix)/(1 + ix)` with
`x = k/γ` (`mw_eq_cayley`), a phase (`cayley_unimodular`). Only coupling ratios are data. With
this generator the PDG CKM gives a flux of `49.1 ± 1.1°` and `K₁₃/K₁₂ = 0.0185 ± 0.0005`;
`VubSeriesPath`'s `(1/(2α⁻¹ + π))/(π/14) = 0.0161` is `4.7σ` low, so its agreement with `|V_ub|` is
with the full amplitude (which includes the route through the in-cycle pair), not with the path it
constructs. Retired as structural; the formula stays as a numerical observation. These numbers are
external fits conditional on two premises, zero-energy scattering on generation leads and equal lead
widths, neither derived (`TransferGenerator`).

**Derived inputs and Wolfenstein.** `FlavourInvariants` shows the numerals in the
six supplied flavour formulas are the Paper I invariants evaluated; the functional
forms themselves are ansätze, not E8 theorems. Upstream
`PMConstants.FlavourDressing` identifies `515/516` as the reference deficit over the spatial
outlets `1 − (1−η)/(D − 1)`: the minimal dilation has exactly three outlet channels
(`DressingChannels`) and a registered loss puts no weight on the time axis (`DressingEvent`); the
earlier four-axis share `687/688` needs the time comparison to fire. `DressingInheritance`:
the reference's refresh moves along its own axis, which is the time (lepton) axis, so only
charged-current transitions of colour carriers (spatial) are dressed; muon decay and neutral
currents are not, so the deficit does not cancel against `G_F`. Every CKM row and column then
loses `1/516`, within `1σ` of all four measured sums (`row_column_tests`); a dressed `Z → q q̄` is
excluded by `R_ℓ` (`z_pole_undressed`). `Wolfenstein` defines
λ, A, ρ̄, η̄ on the paper's own matrix and proves `η̄ > ρ̄` (from `σ > 2χ`) and the
`O(λ³)` truncation structure. `WolfensteinOctant` proves the solar/atmospheric/
reactor octants, and that the solar octant is exactly `1 < φ < 2`.
`ReferenceFlavour.column2_difference_conj` shows the persistence balance is blind
to `sign(sin δ)`, so the CP branch is a separate substrate-orientation input.

**Where the mixing comes from.** `GenerationLabel`: `E₈` roots conserve the generation label, so a
generation change needs a single-wall carrier move of the class two generations share (a glue-label
operation; identifying it with the charged current is open). `ExchangeAxis`: only the pair
mixing through the reference's class mixes inside the cycle; the other two cross the reference
node. `ExchangeChirality`: their `s`/`c` split is the charged current's parity violation.
`NodeElimination`: the quark node-crossing mixings are amplitudes `∝ α` (two legs), a
lepton-axis state's mixing a probability `∝ α` (one leg; the reactor angle). The data-based
`NodePassage` that chose between the readings was removed. `KronSeries`: a conserving link
is a Laplacian, so eliminating the node is Kron reduction and a quark coupling is a series
admittance; `VubSeriesPath`: the path admittance `1/(2α⁻¹ + π)` (two node legs and a unit boundary in
series) is derived.
Candidates: `VcbEnvelope` (`|V_cb|` as a refresh-tick envelope over the free cycle),
`HalfTurnMixing` and `HalfTurnAperture` (the in-cycle mixings as the half-turn refresh shared over
the type-preserving channels: `s₁₂ = π/14`, `sin²θ₁₂ = π/10`, with `π` a length along boundaries
and an aperture through the refresh), `ReactorConductance` (the reactor angle as a node conductance
into the spatial outlets). The modules that picked integers by which fit the data (`MixingTests`,
`ReactorConductance.channel_count_unique`, `VcbEnvelope.drive_unique`, `free_ticks_needed`) were
removed; the remaining comparisons with data are in `E8PConstants.CandidateTests` and
`E8PConstants.FlavourPulls`.

**Current chirality tied to Paper II.** `WeakCurrentBridge.spinProjector_eq_PL`: the
native flavour current's chiral projector is Paper II's `P_L` **within Paper II's
chosen four-component representation**. PMAction
`ChiralityConvention.projector_unique_on_kernel` now forces that projector on the
zero kernel from the reference conditions, and
`projector_eq_fromBlocks_PL` matches it to block-diagonal `P_L`. Attaching the weak
representation is derived (`PMConstants.WeakUniform`), and `PMAction.ChiralLightBand` extends the
projector to the light band through first order in `k`. The projector is rank two, so `modelCurrent G = P_L ⊗ G` is inherited within
that representation, not chosen separately.

**CP for the next papers.** `Downstream`: `pmJ > 0` (CKM CP violated, positive
Jarlskog → baryon-asymmetry sign), `cp_conserved_iff` (`pmJ = 0 ↔ sin δ = 0`), and
the leptonic side `PMNS.jarlskog_nonpos` (opposite sign to CKM).

**Falsifiable ledger.** `FalsifiablePredictions.prediction_ledger` bundles every
measured-input-free claim, conditional on the model inputs above, in one conjunction — the auditable input
to a data fit (the fit itself is data work, outside the axiom-checked tree).

## What is *not* derived

`φ = (1+√5)/2` is now derived from pentagon Ptolemy and the explicit 600-cell
pentagon (`GoldenGeometry`, `SixHundredCell`). Status of each mixing observable (the operator it
refers to in brackets):
* `s₁₂ = π/14` [`2K₁₂/γ`], `sin²θ₁₂ = π/10`: candidates with listed premises (`HalfTurnAperture`);
* `|V_ub|`: the path admittance is derived; its identification with `|S₁₃|` is not (`VubSeriesPath`);
* `|V_cb|`: candidate formula, no schedule basis for its reading (`VcbEnvelope`);
* `δ_CKM`: supplied (`arctan(σ/χ)`), no mechanism in the library;
* `sin²θ₁₃ = 3α`: candidate formula with named outlets and readout (`ReactorConductance`);
* `sin²θ₂₃`: supplied (`PMNSGeometry`), no construction.
`FlavourInvariants` only removes the literal-numeral duplication. The `515/516` Cabibbo dressing is
derived (`DressingEvent`, `DressingInheritance`) under one premise, that carrier space and the
lattice share axis labels (not that a carrier label change is a site move). The absolute wall-mass
scale is an input: ratios are E8 (`PMAction.WallMassRatio`), but no cost functional fixes the
magnitudes, and the scale is an external unit like `m_e`. Link
eigenvalues are not the physical energy scale, so the `π/43` chord bound is about
energies. The V−A projector is forced on the zero kernel by reference persistence
(PM-2 `ChiralityConvention.projector_unique_on_kernel`); attaching it to the weak representation
is derived (`PMConstants.WeakUniform`, `CarrierActions.weak_chiral`), and it extends to the light
band through first order in `k` (`PMAction.ChiralLightBand`). The neutrino
Dirac-survival result is conditional on the upstream
flux/one-link hypercharge representation; the `Y_L` sign is an `e`/`ν` convention
(`ReferenceLink.standard_or_conjugate`), not a physical choice. Measured PDG/NuFIT
comparisons live in the `FlavourPulls` and `ExperimentalPulls` leaves and are not
imported by the CKM/PMNS derivation modules; no measured number enters the
derivation closure.

## Downstream handoff

`PM-5-Decay` and `PM-6-Cosmo` both build against this tree. Paper IV supplies
them the CP input (`Downstream`), external-state on-shellness
(`persistent_single_frequency`), unitarity/mixing (`PMNS`, `CKM`), and Jarlskog
bounds. Their remaining work is their own physical modelling (interaction,
phase-space measure, decay-law cost for V; background/perturbation/baryon dynamics
for VI) — not missing Paper IV proofs.

## Verification

Run `./build.sh PMFlavor` for this library. The top-level `./build.sh audit` checks
the whole tree, not just PMFlavor. PMFlavor may import PMElementaryParticles, not PMHadrons and later; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
