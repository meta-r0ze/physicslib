# PMAction — overview of checked results

The single map of what Paper II proves and what later papers can reuse. Open work
is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md); build instructions are in
[`README.md`](README.md). Canonical sources are under `PMAction/`, imported by
`PMAction.lean`; there are no separate research copies. Theorem names are entry
points, not exhaustive lists. Lean source is the ground truth.

## Scope

- `ReferenceSelection.readPair_run` projects each native port pair onto the live/record stream at every tick. `native_reference_forever` gives exact maintenance on a moving homogeneous lattice routing when the indicated record bank is uniform. Physical bank allocation is tracked in the [machine review](Machine/REVIEW-AND-NEXT.md).
- `PolarizationContact.finite_routing_cancel` gives exact longitudinal cancellation on a finite grid when the probe shift permutes grid points, the vertex and propagator respect wrapping, and denominators are nonzero.
- `FinitePolarization` constructs the full coordinate momentum torus `Fin 4 → ZMod N` for every nonzero `N`, using the D₄ symbol, line-averaged current and contact vertex. Integer winding identities prove the propagator and vertex wrap laws (`symbol_wrap`, `leg_wrap`). Adding a positive momentum-independent regulator to both inverse propagators preserves the Ward cancellation with every grid point retained (`finite_cancel`). Removing that regulator after the full longitudinal sum gives zero (`zero_regulator_limit`). The construction uses the periodic coordinate torus. Physical volume normalization and the transverse-continuum comparison remain open.
- `FinitePolarizationTensor` constructs the full real response matrix of the supplied scalar-link bubble-minus-contact kernel. `response_tensor` reconstructs its response to every pair of probe directions as `uᵀ Π v`. `tensor_symmetric` proves symmetry, and `left_transverse` and `right_transverse` prove both Ward contractions vanish on every nonzero finite periodic grid at positive regulator. The overall physical normalization and transverse continuum coefficient remain open.
- `D4MomentumMeasure` derives the reciprocal basis from `LatticeSiteAction.basisR` and its proved inverse. `dual_pairing` gives the exact `2π` pairing with the physical site basis, `reciprocal_unique` proves uniqueness under that pairing, and `reciprocal_cell_volume` gives reciprocal volume `(2π/a)⁴/2`. For `N` periods along each primitive generator, `primitive_weight` gives Fourier sample weight `1/(2 a⁴ N⁴)`; `inverse_torus_volume` and `total_weight` verify the volume and mode-count normalization. `primitiveMomentum` supplies that grid's momentum map. Identifying it with the coordinate-period response grid requires matching their physical periods.
- `PrimitivePolarization` constructs the scalar-link response directly on `N` periods along each physical D₄ site generator. `root_coordinates` certifies integral coordinates for every hopping root in `LatticeSiteAction.basisZ`; `root_projection`, `symbol_wrap` and `leg_wrap` prove the reciprocal-grid phase and wrapping identities. The response tensor includes `D4MomentumMeasure.sampleWeight`. `weighted_response` reconstructs its physical Fourier-weighted response, and `tensor_symmetric`, `left_transverse`, `right_transverse` prove symmetry and both Ward contractions at positive regulator. This completes a normalized primitive-period finite model. Its transverse continuum and regulator limits remain open.
- The classical gauge continuum theorems in `VaryingFields` and `LinkConsistency` fix the matrix size, representation-valued field and ordinary matrix trace before taking the spacing limit. Shared representation and trace across that limit are part of their parametrization. Selecting the physical group, representation and coupling remains an application premise.
- `NativeDetuning.colour_invariant_flip_zero` excludes a nonzero four-axis matrix that anticommutes with the fixed chirality and is invariant under simultaneous colour-axis permutations of its rows and columns. This applies to an averaged operator as well. For an independent payload index, `WallExchange.payload_symmetry_iff` shows exactly when the full two-detuning Hamiltonian preserves a payload operation: both directed links commute with it. `NativeFlavourWall.native_payload_symmetry` verifies sufficiency on the native carrier registers. Downstream, `PMConstants.ColourWallCrossing` checks the packet colour blocks on a generation-only link and gives a native vector-carrier witness excluding faithful simultaneous realization of the original β and colour swap as commuting operations.
- `CyclicSeesaw.crossing_isometry_iff` characterizes a common crossing weight of unit norm by the isometry of its cyclic link.
- `CrossingScale` separates the crossing's map norm from its Hamiltonian rate. The actual gapped block `WallSeesaw.G Y` is Hermitian and has unitary coherent evolution for every link `Y`, including a cyclic link of weight 2 that fails `YᴴY = 1`. Evolution unitarity therefore supplies no unit-norm constraint on the Hamiltonian coupling. A common nonzero real rate can be absorbed into the isolated crossing's time parameter (`rate_time`, `normalize_rate`). A standalone isometric crossing contract, ratios to the other Hamiltonian terms, and a clock calibration require their own premises.
- `NativeWallOffset.generator_split` embeds the existing lazy-event generator on one wall and retains the exact scalar offset `gap(p)/2` on that wall. On nonempty walls a nonzero offset is unequal to every global scalar shift (`global_shift_iff`). It commutes with an arbitrary Hermitian coupled block exactly when the offset coefficient or crossing link vanishes (`offset_commutes_iff`). With `p < 1/2` and `p ≠ 0`, adding the lazy generator differs from adding only its flip part by every possible global energy shift (`coupled_generators_differ`). These are generator statements; a wall-dependent time-dependent frame would also transform the crossing. The remaining physical event identification is tracked under other-wall detuning.
- `CompletionSelection.agreement_iff` characterizes full-operator agreement for an ambient update with the prescribed encoded action: it must fix the invisible complement pointwise.
- `SplitClockBoundary.update_pi` shows that the supplied vacuum-preserving split is momentum-independent at tick `π`. At momentum `(π/2,0,0)` it fails to commute with the Wilson wall Hamiltonian (`noncommuting`), so it equals no exponential `exp(z H)` for any complex scalar `z` (`no_hamiltonian_time`). Universal identification of the split with an exponential of that Hamiltonian is excluded. The diagnostic tick is in generator units. Physical clock calibration and restriction to light modes remain open.
- `CarrierGateCompletion.lookup_admission_iff` and `lookup_table` classify identity completion for all six supplied Weyl words. The admissible word indices are `{1,3,5}` in class 0, `{0,5}` in class 1 and `{2,5}` in class 2. The coordinate embedding distinguishes all carriers, so another permutation word cannot repair a failed case. A single involution pulse fixes the even modes at a phase return or when it preserves every antipodal pair. For a non-returning β pulse this holds exactly in class 1 (`beta_pulse`). These tests leave general coherent circuits and their event prices open.
- `EvenRootPhase` supplies a nonzero antipode-even carrier mode in every class and proves its coordinate readout vanishes (`mode_invisible`). The actual four-orthogonal-root circuit gives this mode the square of its visible-sector phase (`circuit_mode`); the library's `phaseI` gate therefore changes its sign (`phaseI_mode`). `no_independent_i_completion` rules out identity completion of `i · 1` by this four-root family even with independent pulse times and attempt parameters; the visible action forces all four root phases to `i` (`equal_phases_forced`). `no_i_completion` specializes this to a common clock. This is a full-label completion obstruction. Completion of the whole split update, compensation between gate factors and microscopic prices remain open.
- The numerical two-slice comparison in `tools/slice_axial.py` gives a confined slice-current readout of 0.22–0.45 over cube sizes 3–8, compared with 0.83–0.67 for the on-site spin operator. The two prescriptions give different confined observables despite free normalization.

Paper II builds on the Paper I substrate (E8, clock Δ = 43) and supplies generic
finite dynamics, register/current/schedule constructions, gauge and scalar
transport limits, current algebra, and their audit boundaries. It imports nothing
from Papers III–VI; each later paper owns its own physical application.

Main result: `PMAction.Main.hermitian_action_response` — for a supplied finite
Hermitian `H`, unitary transport of a normalized `φ`, with two-branch response
`(1 − Re⟨φ,Uφ⟩)/2 = ‖φ − Uφ‖²/4` and a bounded fourth-order remainder from
`t²‖Hφ‖²`. `LinkEvolution` identifies the spectral transport with `exp(i t H)`.

## Module map (what you can use)

| Area | Canonical modules | Checked result and retained inputs |
| --- | --- | --- |
| Minimal persistent cube | `MinimalCube` | `cube_interior_iff`: an `n³` cube has an interior vertex iff `n ≥ 3`, so `3×3×3` is the smallest volume-persistent cube; vertex counts `1`/`26`/`27` (moved from PMHadrons) | |
| Discrete causal structure | `DiscreteCausal` | The causal preorder on `ℕ × X` induced by the update stencil `Reach` (≤27 sites/tick): `causal_refl`, `causal_trans`, `causal_one_tick`; `CausallyTrapped`; `zero_clock_not_horizon` (a capacity point is not trapped) | Continuum metric / Lorentzian comparison |
| Spatial metric | `SpatialResponse` | Diagonal optical metric `g_ij = n_i² δ_ij = δ_ij/c_i²` from the same capacity ledger; `spatialMetric_from_index`, `spatialMetric_isotropic` (isotropy from an axis-independent load) | The optical-metric reading; off-diagonal shear |
| Coulomb kernel | `CoulombKernel`, `LatticeGreen3D`, `CubeGreen3` | Green's-function interface `Kernel` with `lap_green` and `symm`; `pairEnergy`; concrete 2/3/4-site path kernels `green2/green3/green4` with `pathLap*_green*` (`lap G = δ`); exact rational Dirichlet Green functions on the `2×2×2` interior (`greenCube`, `cubeLap_green`) and on the `3×3×3` cube (`greenCube3`, `cube3Lap_green`, `greenCube3_symm`), namespace `PMAction.LatticeGreen` (moved from PMAtoms) | General path/cycle Green's function; Paper 3 charge source |
| Discrete response law | `ResponseLaw` | Laplacian on the actual axis-neighbour adjacency: `lap_const` (uniform load → no field), `lap_sum_zero` (antisymmetric double sum), `response_source_neutral` (a static source must sum to zero) | The source distribution; continuum limit |
| Gravitational weak field | `WeakField` | Capacity ledger `C=ν−K`, index `ν/C`, clock `C/ν`; the identification `g_00=−(1+2Φ)` for the paper's linearized pair and the exact clock-squared pair; `Φ=−K/ν+K²/(2ν²)`, strictly attractive | The response law selecting the readout; spatial metric, field equation, global causal structure |
| Conservation → continuity | `Continuity` | A conserved comoving charge gives density `N/a³` and `matter_continuity` (`aρ'+3ρ=0`); `matter_w`/`radiation_w`/`vacuum_w` (`w=0,1/3,−1`). | Which per-particle scaling holds; the expansion `a` |
| History and transfer | `Survival`, `SelectedSampling`, `Reconstruction`, `PersistenceSelection` | Conditional history selection and transfer reconstruction; `exp(−β cost)`, `β>0` makes greatest survival equivalent to minimum cost. Cost functional and admissible choices remain inputs. |
| Action response | `Operators`, `CommonResponse`, `HermitianTransport`, `LinkExpansion`, `LinkEvolution`, `MainTheorem` | Hermitian evolution, comparison response and controlled quadratic expansion for the supplied generator/readout. |
| Comparison implementation | `ComparisonFactorization`, `BranchGateBoundary`, `BranchMixerSynthesis`, `BranchPulseContract`, `ControllerHamiltonian` | Exact Hadamard-test factorization and conditional pulse construction; permutations and diagonal phases alone cannot synthesize the branch mixer. Admission, locality and prices are separate. |
| Restoration and pricing | `FiniteRestorationBridge`, `DifferentialRestoration`, `FiniteLinearizationBoundary`, `CoherentComparisonRepair`, `RestorationResponse`, `EventAccounting`, `CarrierEvents`, `CarrierCost`, `RefreshSchedule` | Finite/differentiable bridges, conservative reset and minimum execution for specified jobs. Net response is not automatically accumulated primitive expenditure. |
| Carrier readout | `SubstrateReflection`, `CarrierReferenceCycle`, `CarrierProbe`, `ClockControlledRoot`, `MatchedLatticeProbe`, `ScheduledReadout`, `ReadoutGateBoundary`, `ParityReadoutCircuit`, `InBandRootReadout` | Actual-root events and conditional probes/readouts; an autonomous clock trace alone does not measure a nonconstant carrier bit. |
| Root reconstruction | `RootTransfer`, `RootTransferPhase`, `RootTransferAccounting`, `RootBranchEncoding`, `RootPulseEvents`, `ActualRootRepair` | Lazy statistical root transfer, logarithmic generator, quarter-phase preparation and carrier repair; label-change and comparison events have distinct probabilities. |
| Finite reference protocol | `RecordTransport`, `WalkRecordTransport`, `WalkReferenceCoupling`, `WalkReferenceProtocol`, `WalkReferenceCycle`, `RootWalkEncoding`, `RootCarrierWalk`, `RootCarrierCycle` | Exact FIFO retention, sharp finite-memory horizon, coupling and full reference walk. No irreversible erasure or free fresh records inferred. |
| Native states and sources | `RootReferencePreparation`, `ReferenceSourceBoundary`, `NativeCarrierProtocol`, `NativeCarrierState`, `NativeReferenceBackground`, `FullCarrierIdentification` | Known-seed conversion; reversible native configurations and one-hot amplitude lift; stationary reference classification and conditional minimization; obstructions to full-space root/Clifford identifications. |
| Continuing record supply | `RecordSupply`, `HomogeneousRouting`, `OpenReferenceFlow`, `PrimitiveRecordBoundary` | Disturbances exported into records; for the specified routing/clean-record contract, exact maintenance forever iff the backward orbit is open; finite substrates return. Homogeneous routings are translations **under an explicit homogeneity hypothesis**. |
| Intrinsic vacuum representation | `CarrierParity`, `CarrierWeyl`, `SubstrateWeylRoots`, `OrthogonalRootPhase`, `OddCarrierPhase`, `CarrierClifford`, `CarrierVacuumSector`, `CarrierVacuumEvolution`, `RectangularEvolution`, `CarrierReadoutQuotient` | Coordinate-odd carrier representation, native generators, full Hamiltonian and exponential intertwining. Physical observations, admitted phases, class/wall allocation and cross-sector coupling remain choices. |
| Full-label observation and locality | `StateIdentification`, `LocalIsometricDynamics`, `ExponentialLocality`, `NativeLocalityBoundary` | Exact observation and two full-label completions. The directional-exponential choice has tails; the on-site isometric/identity-complement choice is unitary with the original finite stencil, all-state readout and no added labels. Primitive admission/prices remain open. |
| Fermion spectrum and split | `Dirac`, `DomainWall`, `DetuningMass`, `DomainWallSpectrum`, `ConfinedCarrier`, `ConfinedWalk`, `ConcreteFermion`, `ConcreteSpectrum`, `SignedSpectrum`, `EnergyCounts`, `WallDispersion`, `DiracEnergy`, `WallSeesaw`, `WallExchange` | Supplied two-wall Hamiltonian, signed branches, positive-state existence, link-dependent seesaw and parity-combined covariance. Representation, link and occupied branches are not selected by these spectrum modules; statistics is a separate premise (`CarrierStatistics`: exchange sign under the exchange-as-relative-turn reading). |
| Controlled propagation | `LocalUnitary`, `SplitUpdate`, `PropagationBounds`, `WilsonSplit`, `VacuumSplit`, `VacuumGenerator`, `VacuumUniform`, `GlobalTickInterval`, `VacuumIteration`, `VacuumErrorRate`, `RealSpaceFourier`, `SpatialContinuum`, `ProjectedEvolution`, `JointSpaceTime`, `SplitCovariance`, `ReferenceWalkParity` | Corrected local unitary split, global safe-tick existence, uniform time-refinement bound, torus Fourier/spectrum identification, branch dispersion and joint fixed-momentum vacuum-sector evolution. Physical refinement/clock and full field/interacting limits remain open. |
| Chiral anomaly on the substrate | `FermionFlip`, `WallTransfer`, `InertiaStability` | Fermion statistics make the many-flavour flip amplitude `det M` (`flip_amplitude`); chirality changes only by transfer between the walls and a flavour-blind background transfers equally (`chirality_change`, `flavour_blind_transfer`), so a winding-`n` history carries `(det M)ⁿ`; the negative-mode count of an invertible Hermitian family is locally constant (`negCount_locallyConstant`, Sylvester's inertia), giving an integer charge without Lüscher. |
| Gauge and scalar transport | `D4Gauge`, `GaugeContinuum`, `VaryingFields`, `LinkConsistency`, `GaugeTransport`, `ReferenceSampling`, `SummedReference`, `ReadoutAdditivity`, `ScalarTransport`, `CompactTransport` | Pointwise D₄ density limits, cubic-consistent link robustness, link extraction from a supplied linear hop, reference readout and scalar kinetic normalization. `CompactTransport.compact_transport_premises`: transports of a compactly supported C² connection are cubically consistent with it and it is `C^{1,1}`, so those two premises reduce to "the links are transports". |
| Gauge fluctuations and running | `RunningCoefficients`, `RunningResponse`, `ContactRunning`, `ContactFierz`, `LoopMeasure`, `LeadingLog`, `PolarizationAverage`, `ShellMoments`, `PolarizationRemainder`, `Polarization*` (subtracted lattice chain, ending in `PolarizationShellIntegral`), `FlatPersistence`, `GaugeFluctuation`, `FluctuationPremises`, `FluctuationClosure`, `ContinuumFields`, `LandauDegeneracy`, `LatticeToContinuum` | Spin/orbital kernel coefficients, gauge-fixed Hessian and Ward algebra, finite-dimensional ghost determinant power, concrete field identities, strip-centre density and pointwise lattice-to-continuum second variation. No quantum continuum measure or integrated lattice action limit. |
| Currents and decay foundations | `ChargedCurrent`, `NeutralCurrent`, `ContactMatching`, `WallChiralCurrent`, `ChiralityConvention`, `ChiralLightBand`, `VATrace`, `MassiveVATrace`, `SpinorCompleteness`, `AmplitudeTrace`, `WeakVertex` | Charged/neutral normalization, su(2) doublet algebra (`T3`, `commutator_*`, `anticommutator_Tp_Tm`), V−A projector `P_L` (idempotent/Hermitian/rank two), wall-projector algebra, spin sums, bilinear-to-trace amplitude and factor 64, contact matching and kernel-basis existence. `ChiralityConvention.projector_eq_fromBlocks_PL` identifies the wall projector with block-diagonal `P_L`; `projector_unique_on_kernel` forces it on the zero kernel from the reference conditions; `ChiralLightBand` extends it to the light band through first order in `k` (the projected Hamiltonian commutes with the wall chirality). Physical interaction, mediator, external states and phase-space remain application inputs. |

## Shared state/controller and register layer

`FiniteEncoding` owns sparse label encodings, coherent isometry, pairing, recovery
and permutation/readout intertwining (Paper III reuses it). `SectorObservation`
combines dependent native sectors without identifying labels; `CarrierClassBundle`
applies it to all three glue classes (48 labels, 24 observed modes). `InvolutionComparison`
and `SpatialComparison` give exact comparison circuits for spectral phases of
involutions, with no independent branch marker.

`IndependentRegisters`, `TensorObservation`, `RegisterPrograms` construct two
disjoint Boolean register banks with exact tensor/composed readout;
`RegisterHamiltonian` lifts any supplied Hermitian generator to occupation-dependent
register hops with unitary evolution and conservation of occupation/payload bits.
`RegisterVacuum`, `RegisterInteraction`, `ChiralRegisterCurrent`, `ClockDynamics`,
`RegisterSplit`, `RegisterReference`, `RegisterControl` give the full native
generator/readout, both-bank interactions, chiral charge on the zero kernel and the
exchanged reference, the four-phase clock, and joint configuration controls.
`RegisterReference` counts `16·|X| + |payload|·|record|` Boolean registers; the clock
is separate. These are compatible finite constructions with **supplied** banks,
amplitudes, charge and admission; they do not select or prepare them.

`PersistenceSelection`, `PersistentBackground`, `CompletionSelection` give
family-restricted selection with the real admissible family; `ReversibleStationarity`
shows closed injective updates cannot finitely prepare a stationary state.

## Spectrum, split and locality (from the former SPECTRUM map)

- `ConcreteFermion` checks the Hermitian β/γ/α Clifford algebra and the concrete
  eight-component two-wall Hamiltonian; the zero-momentum kernel is `((u0,u1,0,0),(0,0,u2,u3))`.
- `DomainWallSpectrum` cancels cross terms: `(H²−(s+δ²)I)(H²−(s+δ²+1)I) = δ²I`.
  `ConcreteSpectrum`/`SignedSpectrum`/`EnergyCounts` give the characteristic
  polynomials and multiplicities; four kernel dimensions are **not** four species.
- `LocalUnitary`, `SplitUpdate`, `PropagationBounds`: unitary involutive
  nearest-neighbour factors, ≤27-site dependence per tick.
- `VacuumSplit`: corrected split `U(t)=onsite(Q(t))R₀R₁R₂` with exact zero-momentum
  `exp(−itW)`; `VacuumIteration`/`VacuumErrorRate` give a momentum-independent
  `C T²/N` bound; `SplitGap`/`GlobalTickInterval` give a safe tick interval (endpoint
  qualitative, physical tick not selected).
- `RealSpaceFourier`, `SpatialContinuum`, `JointSpaceTime`: exact torus update and
  momentum blocks, branch dispersion, and fixed-momentum joint limit
  (`a→0`, `1/(a²N)→0`; explicit family `a=1/(r+1)`, `N=(r+1)³` via `ProjectedEvolution`).
- `WallDispersion`, `DiracEnergy`, `WallSeesaw`, `WallExchange`, `SplitCovariance`:
  exact nonzero-link masses `m₊²+m₋²=y²+2δ²`, `m₊²m₋²=δ⁴`, positive eigenstates,
  multi-flavour seesaw, parity-combined covariance. `WallRanks`: eigenspace ranks from the trace
  certificates. Candidate wall-mass models (moved from PMFlavor): `WallEnergy` (the energy
  `√(p² + m²)` of a wall branch), `WallMassModel` (the branch-energy impedance at momentum `p`),
  `WallImpedanceChoice` (zero-momentum mass ratio versus energy ratio), `WallMassRatio` (the wall
  couplings if the mass ratio is the capacity ratio `16/21`). `Y` is the chirality-flipping (mass) term;
  whether it also carries generation mixing is open (`WallSeesaw` docstring).
- `WallHopPhase`: on one chirality the Wilson term drops out (`sandwich_beta`) and an in-wall hop
  is a quarter turn times a Hermitian matrix (`chiral_hop`); two such legs give a real reduced
  coupling (`quarter_turns_cancel`), so in-wall kinetic hops give no CP flux.
- `GenerationSector`: moves on the generation labels (glue classes on the two walls). `E₈`
  translations conserve the label and keep a generation state only for `a ∈ {0, label}`
  (`glue_keeps_iff`); translation by the label swaps the walls' classes (`label_glue_swaps`), keeping the label and
  reversing the orientation (between the two conventions, not within one). Generation changes need a single-wall `D₄*`
  carrier equal to the other wall's class (`shift_keeps_iff`, `shift2_keeps_iff`).
  Built on it (generation-sector plan, done): `PMAction.GenerationOrientation` (the two encodings
  agree; `GenerationWalls`' index is the label with the orientation frozen), `GenerationMass` (the
  diagonal mass is a composite: equal-class crossing plus a carrier of the label class),
  `GenerationCurrent` and `GenerationWeak` (generation changes are a carrier plus a glue move; the
  weak vector carrier makes only the light-pair change), `GenerationParity` (within one convention
  the crossing link is one-directional, never Hermitian), and `PMAction.CyclicSeesaw` (the seesaw on
  that link: masses `δ²/|y_h|`, equal for a class-independent crossing; `det Y` the product of the
  amplitudes).
- `CarrierFlip`: an in-wall hop `−(i αⱼ + r β)/2` is a kinetic part `−(i/2) αⱼ`, which commutes
  with `Γ` (keeps chirality, no mass), plus a Wilson part `−(r/2) β`, which anticommutes with `Γ` and
  is the on-site mass operator (`hop_split`, `keep_commutes`, `flip_anticommutes`). So a carrier hop
  of amplitude `t` puts `−r t/2` in the slot of `δβ`: the premise of `PMAction.CompositeMass`, for a
  carrier of this Wilson form. At `r = 1` the composite mass ratios are the carrier amplitude ratios.
- `ReferenceDetuning`: with a separate on-site detuning per wall, `Hw δ₁ δ₂` (`Hw_equal`: equal
  values give `hamiltonian 0 δ`), the second-wall reference background `(0, 0, a, b)` is sent to
  `δ₂ (a, b, 0, 0)` (`second_wall_action`), so it is a zero mode exactly when `δ₂ = 0`
  (`stationary_iff`); the other wall's detuning is free. If the reference persists as a stationary
  zero mode of the update the flavour fermions see, the on-site chirality flip lives only on the
  wall without the reference: the maximal wall asymmetry `PMAction.LightSplit` needs, from a
  structural source.
- `ReferenceWallRotation`: with `M = D_R (δ_O + cyc κ_O)` (`ReferenceWallMass`), the reference-wall
  Gram matrix is `D_R (X Xᴴ) D_Rᴴ` (`left_gram`); `cyc κ (cyc κ)ᴴ` is diagonal (`cyc_gram_offdiag`), so
  each off-diagonal entry is `dᵢ (δ̄ (cyc κ)ᵢⱼ + δ conj (cyc κ)ⱼᵢ) d̄ⱼ` (`left_gram_entry`): first order
  in the carriers and scaled by `dᵢ d̄ⱼ`. The persistence rotation on the reference's wall is then about
  `|dᵢ/dⱼ| · |κ_O/δ_O|` (perturbative reading), suppressed by the label states' mass ratio.
- `CertainTransferRate`: a two-state transfer `sin²(tτ)` is certain iff `cos(tτ) = 0` (`certain_iff`),
  so a certain event of duration `τ` has `tτ ≥ π/2` (`certain_min`) and flip at least `rπ/(4τ)`
  (`flip_lower`). Admittance (`NodeAmplitude`'s `K = 1`) fixes the carrier's rate only with the event's
  duration.
- `WireMass`: the wire's light mass as one definition, `mass δ κ_R κ_O = diag κ_R (δ + cyc (shift κ_O))`,
  with the other wall's carriers placed by glue arithmetic on single-wall modes (`single_wall_class`:
  the move between generations `h`, `h + 1` has class `e h`; `shift κ_O h = κ_O h`, `shift_entry`; the
  vector carrier joins the heavy label to label `1`, `vector_on_heavy_edge`). `undetuned`: at `δ = 0` it
  is `UndetunedWall.undetuned_masses`; `det_mass`: `κ_R 0 κ_R 1 κ_R 2 (δ³ + κ_O 0 κ_O 1 κ_O 2)`.
- `WireLightBound`: for the derived wire with `K = 1`, carriers `(1, k, k)`, real `δ ≥ 0` and
  `0 < k ≤ 1/10`, the eigenvalues `a ≤ b` of `M Mᵀ` (Mathlib's Hermitian eigenvalues; `vieta`,
  `eig_nonneg`) satisfy `k² b ≤ 2a` (`eigen_ratio_bound`): lightest-to-middle mass ratio `≥ k/√2`. Steps:
  `vieta_ratio` (`3e₂² a ≥ e₁e₃ b` for ordered positive roots), `gram`, `e1_eq`, `e2_eq`, `e3_eq`, `poly_bound`
  (an explicit sum-of-nonnegative-terms certificate); `M_eq` ties `M` to `WireMass.mass`.
- `SignFlip`: a sign flip `x ↦ −x` on a wall is a trivial-class glue move (`neg_class`,
  `flip_move_trivial`), keeps every generation state and its label (`flip_keeps_state`), and is no
  label change (`flip_not_label_change`).
- `LightPairTexture` (not the wire's placement; kept as the algebra of a vector carrier on the light
  pair): the light block is `k [[δ, 0], [K, δ]]`; its Gram matrix
  (`gram`) has light states `(t, 1)`, `(1, −t)` with masses `δ/t`, `δ t` when `δ(1 − t²) = t`
  (`light_vectors`, `ratio`): `tan θ₁₂ = √(m₁/m₂)` at leading order.
- `NativeDetuning`: the on-site detuning is the rate of a native `β` event (`generator_split`,
  `gap_zero_iff`); `β` swaps carrier axes `0 ↔ 2`, `1 ↔ 3` (`beta_swaps_axes`) and moves `4` of `8`
  vector carriers across the reference axis, no spinor carrier (`beta_crossings`).
- `WilsonPointForced`: the Wilson-`r` neighbour coefficient squares to `(r² − 1)/4` (`coeff_sq`), so
  the split update's exact local unitarity forces `|r| = 1` on every wall (`nilpotent_iff`).
- `LightLeakage`: for a symmetric gapped block with `G² = g²` (`norm_map_of_sq`), `G − E` is coercive
  (`coercive`), so a light eigenstate's gapped part is at most `v/(|g| − |E|)` (`leakage_bound`). For
  the wire: allowed leakage `L` holds once the largest flip is `≤ √(L/(1−L)) (|y| − |E|)`.
- `FiniteVertex`, `PolarizationContact`: the finite-`q` current vertex of the link Laplacian. The
  Ward identity is exact (`ward`, `leg_ward`): the conserved vertex is the midpoint vertex with each
  root weighted by `sinc(a r·q/2)`; the midpoint vertex alone misses it by `O(a²|k||q|³)`
  (`midpoint_gap`). The two-field contact term is the mixed second variation of the cosine link
  (`link_second_variation`), with its own Ward identity (`contact_ward`: it is the difference of the
  two shifted legs). Contracting bubble minus contact leaves the difference of two momentum routings
  (`bubble_sub_contact`), which cancels by a shift on the full zone but not on a cut shell.
- **Subtracted lattice polarization** (`PolarizationIngredients` … `PolarizationShellIntegral`). The
  lattice integrand `latInt` (sinc-weighted legs over `S(k) S(k + q)` minus the contact over `S(k)`,
  unit probes `e_μ`, `e_ν`) with its `q = 0` value subtracted, integrated over the continuum shell
  `lo < |k| < hi`, against the continuum's orbital term. Chain: per-root expansions in
  `x = a r·q/2` (`PolarizationTaylor`, `PolarizationSplit`), each order against the continuum
  (`PolarizationOrders`), the exact assembly `L = L₀ + Lin + Q + R` with the odd part cancelling in
  the second difference (`PolarizationAssembly`), magnitudes in the ℓ¹ size `n(w)`
  (`PolarizationMagnitudes`), the cubic rest `≤ P(1) n(q)³/n(k)⁵` (`PolarizationCubic`,
  `PolarizationShellCubic`), `|Q_lat − Q_cont| ≤ K a² n(q)²/n(k)²` (`PolarizationQDiff`,
  `PolarizationShellQ`, `PolarizationGapSizes`), the pointwise bound (`PolarizationPointwise`), its
  Euclidean form `≤ (4K a² hi² |q|² + 8P(1) |q|³/lo) |k|⁻⁴` (`shell_pointwise`), the reflection
  `latInt a (−q) μ ν (−k) = latInt a q μ ν k` (`latInt_reflect`, `int_reflect`), and integrability.
  Result (`shell_integral`): for `0 < lo ≤ hi`, `4|q| ≤ lo`, `2 a hi ≤ 1`,
  `|∫_shell (L(q) − L(0)) − (−1/3)(|q|² δ_μν − q_μ q_ν)·2π² ln(hi/lo)|
   ≤ (4K a² hi² |q|² + 8P(1) |q|³/lo)·2π² ln(hi/lo)`, with `K = 271853128/3`,
  `P(1) = 47979504985/36` (generated by sympy, not optimized). The `q²` part of the error is
  `O(a² hi²)` per unit `|q|²·2π² ln(hi/lo)`, so it vanishes as `a → 0` at a fixed shell: the
  bound resolves the `q²` coefficient. The constant is crude: it resolves the coefficient only for
  `a·hi ≲ 10⁻⁵`, against the numeric `C ≈ 1.38` of `tools/lattice_polarization_check.py`, and it
  carries `hi² ln(hi/lo)` where the numeric check finds `hi² − lo²`. Scope: the momentum integral is
  the continuum shell, not the Brillouin-zone sum; the bound is component-wise.
- `InertiaCertificate`, `InertiaCongruence`, `WilsonCertificate`: the inertia certificate for the
  winding witness. A strictly row-dominant Hermitian `B` has as many negative modes as negative
  diagonal entries (`negCount_eq_sign_count`: deform the off-diagonal part to zero, Gershgorin keeps
  it invertible, `InertiaStability` keeps the count). Sylvester's law: `negCount (Qᴴ A Q) = negCount A`
  for invertible `A`, `Q` (`negCount_congruence`: the pencil `1 + z(Q − 1)` is singular at finitely
  many `z ∈ ℂ`, whose complement is connected). So `wilson_certificate`: if `B = Qᴴ H Q` is strictly
  row-dominant, then `H` is invertible and its negative count is the sign count of `B`'s diagonal;
  `row_gap_of_squared_error` certifies the rows from one Frobenius bound. No Gram estimate on `Q` is
  needed.
- `TorusWilson`: the Wilson kernel on the `L⁴` torus for any site hops and link values,
  `D = (4r − M)·1 + Σ_μ (T_μ ⊗ −½(r − γ_μ) + T_μᴴ ⊗ −½(r + γ_μ))`, `H = (1 ⊗ γ₅) D`, is Hermitian for
  Hermitian `γ`, `γ₅` with `γ₅` anticommuting (`wilsonH_hermitian`, by Kronecker algebra). The
  certificate script's gammas are the library's: `γⱼ = i β αⱼ`, `γ₃ = β`, `γ₀γ₁γ₂γ₃ = Γ`
  (`script_gamma0_eq` … `script_gamma5_eq`), so its kernel is Hermitian for any links
  (`script_kernel_hermitian`).
- `TorusFlux`: the certificate script's link phases (`phase`, its `phases` formula over `ℚ`) carry
  the stated constant field: at `L = 3`, `(n₁₂, n₃₄) = (1, −1)`, every plaquette in the `(0,1)` plane
  carries `1/9`, in the `(2,3)` plane `−1/9`, elsewhere `0`, mod `1` (`plaquette_flux`; topological
  charge `−1`), and the trivial history none (`plaquette_flux_trivial`).
- `ZeroModeCoupling`: the inter-sector hop `−β(r+Γ)/2` splits into `β(1+Γ)`, which annihilates the
  zero modes (`wilson_kills`), and `β(1−Γ)`, which joins them (`off_wilson_joins`); the direct
  zero-mode coupling is `(r − 1)·βx` (`zero_mode_element`), zero at the Wilson point. A direct
  (non-seesaw) mass is a departure from `r = 1`, the two-slice wall's residual mass.
- `LocalIsometricDynamics`: the finite-stencil full-label completion
  `E U E† + I − E E†` (unitary on all labels, same readout, no extra labels).

## Gauge, Yang–Mills and limits

`GeometricGauge`, `ReciprocalLinks`, `ReciprocalReflection` give the geometric
configuration-space gauge action and Gibbs invariance, with one reciprocal-link
measure that is gauge invariant and site-reflection positive. `LatticeGibbs`,
`LatticeGibbsU1`, `UnitaryHaar` and `SpecialUnitaryHaar` give the finite-volume
Euclidean probability measures for `U(1)`, `U(N)` and `SU(N)` links.
`TransportExistence` constructs global unitary transport from a continuous skew
connection; `CompositionalTransport` derives the ODE and classical limit from
conserving single-hop updates; `NativePacketUpdate` proves those contracts for the
native E8 packet subsystem. `UniformGaugeAction`, `IntegratedGaugeAction`,
`IntegratedScalarAction`, `LatticeSiteAction`, `ClassicalYangMills` give the
site-sum-to-integral limits on a box under explicit regularity.
`QuotientClosure.gibbs_quotient_invariant` proves gauge invariance descends to any
measurable edge-identification quotient compatible with the action.

**The gap half** (modules in [`MassGap/`](MassGap/README.md), namespace `PMAction.MassGap`). `DefectGap` reads Paper I's distinction cost (one transition per boundary
edge, `PMSubstrate.Distinctions.cost_per_cut_edge`) on any finite connected site graph:
`cost_eq_zero_iff` (zero cost exactly on the uniform configurations, the vacuum and its Closure
relabeling), `cost_ge_one` / `gap_uniform_in_volume` (every excitation costs at least one
transition, with the constant independent of the number of sites), `survival_excited` (weight
`≤ p` at hazard-form survival `p` per transition), and `transfer_contracts_excitations` /
`transfer_fixes_vacuum` (the diagonal transfer is the identity on the vacuum and shrinks the
excited sector by `p` in `ℓ²`; decay rate `≥ −log p` per tick, uniform in volume), and
`cost_le_of_defect_subset` (a defect confined to a region `Λ` has cost bounded by the adjacent
pairs touching `Λ` — *local defects cost locally*, the first step of the locality argument).
`GapStability` gives the quadratic-form version under a perturbation `W` with `|W v| ≤ ε‖v‖²`:
`excited_lower`, `vacuum_upper`, `gap_stable` (separation `≥ m − 2ε`), and `gap_pos`
(`ε < m/2`); `DefectGap.gap_survives_offdiagonal` instantiates this at the PM gap `m = 1` (so the
condition is `ε < 1/2`). At `p = exp(−β)` the survival weight is the Gibbs density
`exp(−β·cost)` (`survival_eq_gibbs`, the same as `LatticeGibbs.weight`), so the per-tick gap is
the coupling (`gap_eq_coupling`). This is a gap for PM's diagonal cost, not for the continuum quantum
theory: for a lattice gauge transfer matrix `ε` is extensive, so it is volume-uniform only when
the off-diagonal part is bounded uniformly in volume. This diagonal half is *complementary* to the
linearized Hessian/Schur gap already present (`SplitGap`, `VacuumSchur`, `VacuumLocalGap`,
`JointVacuumGap`, `CompactSplitGap`).

**The substrate gap (closed).** `MassGap/` proves a volume-uniform mass gap for PM's distinction
substrate, carrying the contour route to the end. The PM history sum is a contour polymer gas (`ContourGas`, `HistorySum`). On the
open-time slab it is a transfer-matrix product (`TransferSlab.slab_transfer`), and even parity
observables are sign twists of that gas (`SlabObservables.corr_eq_Z`). A time-decaying
supersolution gives Euclidean clustering (`SlabClustering`), and the spectral assembly
(`SpectralBounds`, `Walsh`, `GapFromCorrelation`) gives `SlabGap.slab_gap`: in the flip-even
sector of `T²` the top eigenvalue `Λ` is simple and every other eigenvalue is `≤ μ² Λ`,
uniformly in volume; with `μ = √q` the bound is `≤ q Λ` (`SlabGap.slab_gap_explicit`, degree
bound proved in `SlabDegree`); on a cubic box with `q = e^{−β}` the mass is `≥ β/2` per tick
(`CubicBox.box_mass_gap`). Scope: this is the distinction substrate. The gauge layer is a separate
continuous field (`NativePacketRouting.pure_permutation_refinement_trivial`; Wilson cost, group and
`β` not derived), so its gap is the quantum Yang–Mills problem in the scope note below.

**Yang–Mills scope.** This branch is a test of persistence mechanics, not a
construction of Yang–Mills theory. Its deliverable is the classical continuum
limit plus the finite-volume Euclidean setup (Gibbs measure, gauge invariance,
site-reflection positivity). The Clay-level items — infinite volume, the
renormalized continuum, full O(4) restoration, Osterwalder–Schrader
reconstruction, the mass gap and nontriviality — are the general
quantum-Yang–Mills problem, not PM-specific consequences, and are out of scope
here. The remaining PM-specific inputs are the two `NativePacketUpdate`
controls/admission premises and the selection of group, representation and β.

## Established results formerly tracked in REVIEW-AND-NEXT (moved Nov 2026)

- **States and observation:** native representation, dependent-sector observation
  (`SectorObservation`), class bundle (`CarrierClassBundle`), odd-carrier sector with identity even
  modes.
- **Completion selection:** `LocalIsometricDynamics` (finite-support on-site completion, unitary on
  all labels, same stencil); `CompletionSelection` (persistence selects it:
  `most_persistent_completion`, `selected_is_identity`).
- **Reference and records:** `RegisterReference`, exact maintenance (`RecordSupply`,
  `HomogeneousRouting`), stationary preparation (`PersistentBackground`, `ReversibleStationarity`),
  unboundedness from persistence (`HomogeneousRouting.forever_iff_open`, `forever_needs_infinite`);
  boundary results `ReferenceSourceBoundary`, `PrimitiveRecordBoundary.cannot_prepare`;
  `ReferenceSelection` (the reference is selected, not prepared; per-tick ledger).
- **Clock:** `RegisterSplit` (four-phase schedule), `ClockDynamics`, `ClockPeriod` (period `Δ`).
- **Gauge transport and OS:** `CompositionalTransport`, `NativePacketUpdate`, `GeometricGauge`,
  `ReciprocalReflection`, `OsterwalderSchrader` (OS semi-inner-product, `os_cauchy_schwarz`), the
  assembled OS quotient (`osCore_normSq_eq`, `mem_osNullSubmodule_iff`, `quotientForm`,
  `quotientInnerProductSpace`), `QuotientClosure.gibbs_quotient_invariant`; per-step maintenance in
  PM-4 (`PerStepContract`).
- **Gap:** `DefectGap`, `GapStability`, and the substrate gap `MassGap.SlabGap.slab_gap_explicit`
  (mass `≥ β/2` per tick, `CubicBox.box_mass_gap`). The gauge layer is a separate continuous field
  (`NativePacketRouting.pure_permutation_refinement_trivial`); its gap is the quantum Yang–Mills
  problem (out of scope, below).
- **Limits:** `JointSpaceTime`, `UniformGaugeAction`, `IntegratedGaugeAction`,
  `IntegratedScalarAction`, `ClassicalYangMills`, `LatticeSiteAction`, `LatticeToContinuum`.
- **Chirality and weak structure:** `projector_unique_on_kernel`, `projector_eq_fromBlocks_PL`,
  `WeakCurrentBridge`, `ReferenceStabilizer.electroweak_stabilizer`.
- **Confined carrier (for the hadrons):** `ConfinedCarrier` (two-slice Hermiticity, the wall
  preserves `Σ_z`, `α₁, α₂` anticommute with it, `axisStep_unitary`, and the fixed-input status
  table: single free carrier `(5/3)⟨Σ_z⟩ = 1.377`, `+8%`, with the rejected fits), `ConfinedWalk`
  (`cube_axisStep_unitary`: the walk on the `3×3×3` cube is unitary for every tick),
  `MinimalCube`; numerics in `tools/confined_carrier.py`, `tools/confined_walk.py` (hard wall from
  the identity completion; small tick forced by isotropy, `VacuumTangent`). The ground mode's rms
  radius `ρ = 1.3535970…` sites is certified with exact and interval arithmetic
  (`tools/carrier_rms_certificate.py`; Lean proof deferred, REVIEW A.1). The on-site `Σ_z` has unit
  spin normalization for free axial motion (`tools/axial_ward.py`); the confined Ward identity is
  open (REVIEW A.2).
- **Flat links:** `FlatPersistence.flat_iff` (zero loop cost iff every holonomy is `1`).
- **Running:** `RunningResponse` (spin `(2s)²` and orbital `−1/3` from the substrate response);
  `ContactRunning` + `ContactFierz` (the weak contact's coefficient `(3/2)(1 + 2Q̄)` from the Ward
  combination and the `16`/`4` Dirac identities, proved on the Weyl blocks via `triple_blk`).
- **States, statistics and readout (B.1):** `ReadoutRule` (an additive, basis-invariant,
  monotone readout weight is `r²`: `born`), `ClassAdmission` (all three glue classes admitted),
  `CarrierStatistics` (exchange is a relative full turn, `−1`; antisymmetry and exclusion).
- **Colour inside a hadron:** `ColourSinglet` (the three-carrier singlet has zero mean colour
  source), with `FlatPersistence`: no colour field on spin at leading order.
- **Loop normalization:** `LoopMeasure` (the 4D measure gives `(α/4π)ln(M²/μ²)`), used by
  `ContactRunning` with the orientation sign. `LeadingLog` derives it on the substrate: the
  self-energy's `½` (so `W = −1`) is the D₄ direction average, not a Feynman parameter
  (`averaged_propagator`, `self_energy_weight`); the link Laplacian's symbol is `|k|²` up to
  `a²|k|⁴/12` (`symbol_gap`); and the D₄ shell `μ < |k| < M` gives `ln(M/μ)/(8π²)` per
  `d⁴k/(2π)⁴` up to `a²(M² − μ²)/(24π²)` (`leading_log`). `PolarizationAverage`: in momentum
  space the vacuum polarization's orbital `−1/3` is the D₄ second and fourth moments
  (`orbital_third`, transverse because D₄ is isotropic to fourth order); the substrate vertex
  `∂symbol` is `2k` up to `O(a²|k|³)` (`vertex_gap`); `running_unit` gives `b₀/(2π)`'s `2π`. `ShellMoments`: the continuum shell's
  angular moments are the D₄ roots' (reflections and polarization give `C = L/4`, `A = L/8`),
  so the shell integral of the polarization integrand is its root average times `∫|k|⁻⁴`
  (`shell_eq_root_average`) and equals `−(1/3)(q²δ − qq)·2π² ln(M/μ)` (`shell_orbital`). `PolarizationRemainder`: the full
  continuum integrand minus its `q`-independent part integrates over the window `2|q| ≤ μ` to that
  orbital term up to `500|q|³/μ · 2π² ln(M/μ)` (`polarization_window`; pointwise
  `scalar_remainder`).
- **Event pricing and admission:** `EventCoupling` (event price to stiffness and coupling,
  moved from PMConstants), `ClockLedger` (a factor costs its flags; the clock `2·toll·m` per tick),
  `Admission` (the split's factors are unitary, local and priced).
- **Lattice kernels:** `CoulombKernel`, `LatticeGreen3D`, `CubeGreen3` (exact `3×3×3` Green
  function).

## Interpretation boundaries (what is *not* selected)

Build success certifies the conditional statements, not physical identification.
Not selected by these theorems: the physical generator/representation, state/readout
contract, carrier/spinor/gauge identification, link/occupied branches and statistics,
bank/occupancy preparation, gate admission, clock calibration, primitive event
tariffs, the current/mediator and decay measure, and the quantum continuum measure /
Lorentzian limit. The V−A projector `P_L` and the su(2) doublet algebra are proved
algebra; `ChiralityConvention.projector_unique_on_kernel` shows the projector is
forced on the zero kernel by the reference; attaching it to the weak interaction is derived
(`PMConstants.WeakUniform`), and `ChiralLightBand` extends it to the light band through first
order in `k`.

## Ownership / downstream boundary

Paper II supplies **generic** dynamics and imports no later paper. Paper III owns
packet representations, sector/resource ownership and constants; Paper IV owns
flavour/mass applications; Paper V owns decay/phase-space/lifetime; Paper VI owns
cosmology. Moving a generic proof upstream does not move an application's physical
identification assumptions. Paper IV's `WeakCurrentBridge` reuses
`WeakVertex.PL` and `VATrace.L_eq` to identify the native flavour-current chiral
projector with `P_L`; the flavour generator and mediator remain Paper IV inputs.

## Verification

Run `./build.sh PMAction` and `./build.sh audit`. No Paper III–VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.

## Results of the 2026-11-16 review (the wire)

- **Carrier placement.** The light mass's right factor acts on the other wall's single-wall modes; the
  move between generations `h`, `h + 1` changes the class by `e h` (`WireMass.single_wall_class`). This
  fixes the placement (`WireMass.shift`). A 2026-11 "correction" that used `GenerationCurrent`'s carrier
  `e (h − 1)` (a two-wall label change with a glue move on both walls) mixed two state spaces and was
  withdrawn, with what was built on it (`LightPairTexture` as the wire's block, the GST relation, the
  margins and second-ratio fits). `LightPairTexture` keeps the algebra of that placement.
- **The weak refresh keeps the label** (`SignFlip`; `PMFlavor.RefreshLabel`).
- **The wire's inputs, tested by persistence.** (a) One `δ_O` per wall: forced in size (one `β` event
  per wall; `β` is an involution on every class). Per class `β` fixes `0`, `4`, `0` of the `8` carriers
  (classes `0`, `1`, `2`), so the eigenbasis differs by class, not the magnitude. (b) `|κ(s)| = |κ(c)|`:
  forced by native intertwining (`CarrierWeyl.intertwining`; `ReferenceLegSymmetry.flag_conj` excludes a
  reference-readout leg asymmetry). (c) The other wall's vector amplitude: a choice; no value fits down
  and leptons together (numerical). (d) `k/K` as a rate (`0.0385`): worse than `α/2` (numerical).
- **Light-ratio bound** (`WireLightBound.eigen_ratio_bound`): for `δ_O ≥ 0` the lightest-to-middle mass
  ratio is at least `k/√2`. For `δ_O < 0` or a cycle phase, `det = k²(δ³ + κ₀κ₁κ₂)` can vanish.
- **Why the wire is odd** (`FullCarrierIdentification`): carrier permutations fix the even uniform mode,
  and anticommuting generators cannot share a fixed mode, so the Dirac structure lives on the odd
  sector. The doublet sign (odd ± even of one carrier) is not a property of a wire mode; it belongs to
  the protocol layer (`PMElementaryParticles.DoubletSign`, `ProtocolReadout`).
- **Two-detuning wall:** `WallExchange.H2`, `NativeFlavourWall.nativeHamiltonian2`, `native_observed2`
  carry separate on-site flips on the two walls.
- **Excluded or withdrawn** (details in git history): the up protocol's undetuned heavy entry (built on
  the withdrawn placement); an on-site term on the reference wall's heavy row (`13×`); economy-minimal
  `δ_O` (a crossover, not a point); reference-readout leg prices as an `s/c` asymmetry.

## Reference-maintenance checks in the protocol layer

The following checks constrain the reference-maintenance route.
- On the wire the maintained reference is `ChiralityConvention.physicalBackground`, a vector of the
  wire's sites, so it is antipode-odd. Any maintenance acting on the wire is therefore blind to the
  doublet sign: `PMElementaryParticles.ProtocolReadout.odd_reference_no_split`. Correction: the
  earlier "reference splits the lepton pair at first order" used the reference *carrier*
  `+2e₀`, which is the channel-layer object, not the wire background.
- The only maintenance that addresses weak partners separately is at the channel layer: the payload
  ledger (`RefreshMap.payload_visit`, `same_payload_readout_iff`: one row per channel). Its weights are
  uniform (`GaugeLedgers`: `η` per payload). The per-channel quantities that differ between partners
  are the carried charge values (`Y_R`, `Q`).
- Test of "maintenance strength is a monotone function of one carried charge" against the light
  detunings (up `0.042` < electron `0.068` < down `0.236`, from `m₁/m₂` alone): `|Y_R|` orders
  (electron `2`, up `4/3`, down `2/3`), `|Q|` (electron `1`, up `2/3`, down `1/3`), signed `Y_R` and signed
  `Q` order the three as electron, down, up. None puts the protocols in data order, so a monotone
  function of a single charge is excluded. Colour plus a charge (two factors) is not excluded but has
  one lepton point, so it is not testable yet.

The unresolved channel-layer maintenance strength is a dependency of the wire detuning item in REVIEW-AND-NEXT.
