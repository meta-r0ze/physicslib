# PMConstants — overview of checked results

The module map for Paper III's constants, sectors, running and gauge factors. Build
instructions are in [`README.md`](README.md); the constant-by-constant open
dependencies are in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md).

## Entry points

- `CurrentConstants.current_snapshot`: the current manuscript values.
- `E8Values`: partition constants written from `D, Δ, ν, σ, χ, R_M` with equality bridges.
- `ElectroweakE8`: canonical electroweak constants written from the E8 record.
- `FlavourDressing`: the per-direction reference deficit `1 − (1−η)/D = 687/688`.
- `TableConsequences.end_to_end`: the weak fraction from the derived requirement table.
- `ChainCouplings.chain_couplings`: all three couplings from Paper II's D₄ gauge action.
- `SectorObligations`: the reference/update contract (exact refresh, weak ownership, colour reads).
- `ReadScale`, `OnShell`: the matching scales from persistence and frame independence.
- `VevEntry`: how the vacuum value enters the fermion masses (law A).
- `GenerationEncoding`: exhaustive three-pair classification, the distinction between
  pair types and independent physical generations, and exact retained-label storage.
- `GenerationHistory`: an actual companion-carrier encoding, its coherent isometry,
  and the generation-preserving action of native within-class root words.
- `GenerationWalls`: a representation on two-wall carrier labels, its two balanced
  incidence conventions, and the nontrivial action of wall exchange.
- `GenerationVacuumChoice`: tests the pair contract against Paper II's actual
  class-sector vacuum and its unbroken class degeneracy.
- `CarrierPhaseComparison`: the exact marker-free root-phase circuit and supplied
  two-cell comparison register applied to the actual packet permutations.
- `CarrierRegisterModel`: separate occupied Boolean banks for actual vacuum and
  packet labels; exact coherent readout for the beta word and packet operations.
- `CarrierRegisterVacuum`: the full native vacuum generator lifted to those banks,
  with unitary evolution and exact all-state readout.
- `CarrierRegisterChirality`: tests of packet/wall/chirality matching against the
  full vacuum, and the agreement of the matching rules on its zero kernel.

## Next physical dependency for flavour

Three unordered distinct-class pairs are exactly three possible packet types.
`GenerationEncoding` proves that retaining all their independent generation/carrier
labels gives 48 modes, whereas the three minimal glue classes contain 24 native
labels. Every native carrier occurs in two packets. No injective native-only
encoding exists, including a linear encoding of coherent amplitudes. An explicit
encoding by native carrier × one binary tag preserves the complete complex pairing;
two tag values are necessary. This is a representation/storage theorem, not a free
physical gate or a selection of an extra memory factor.

Also, `Generations.same_class_loses` concerns the vector-only readout: keeping the
wall tag preserves distinctions in an equal-class packet. Conservation alone does
not exclude such packets. The three-pair classification therefore retains the
vector-faithful, unordered, distinct-class packet contract. Identifying the physical
generation states and their update, then deriving its breaking law, remains the
relevant prerequisite for Paper IV's parameter selection. Completion of gravity or
the thermal-floor example is not required for that work.

`GenerationHistory` gives a concrete retained-record route: a supplied reference
carrier in the companion occupied class encodes the missing binary distinction.
The map has an exact left inverse and its coherent embedding has E†E = I.
Its physical record preparation, location and renewal still need a model. Every
word in the tested native within-class simple-root gate set preserves the pair
type, including at the amplitude-matrix level. Thus this representation supplies
no generation mixing until a class-changing or relational update is identified.

The binary distinction need not be additional memory. `GenerationWalls` gives an
exact amplitude-preserving representation on wall × native carrier, using all
three classes on both walls and one class per wall in each packet. Precisely two
balanced incidence conventions work, related by wall-name exchange. However,
within either fixed convention, exchanging walls while keeping the carrier class
fixed changes the packet label in a class-dependent way. It cannot be treated as
an independent generation-preserving wall swap without a further identification.
This is a possible representation, not a proof of physical accessibility or of
the flavour current and full vacuum update on that representation.

## New shared route from Paper II

The generic coherent encoding proof, the unique-control maintenance theorem and
the two-frequency ray theorem now live canonically in Paper II. Their old Paper
III names remain available. Paper III retains all packet/reference choices and
constant-specific arithmetic.

`CarrierPhaseComparison` now has an exact comparison construction for the
packet's involutive operations without an independent branch Z marker. It uses
Paper II's reconstructed root phases, and a spatial two-cell register is available
without borrowing the chirality wall. Admission, clean-cell preparation, clock
matching and the total primitive ledger remain inputs; nine forward spectral
calls are not priced as nine primitive events.

The simpler generation candidate is Paper II's direct bundle of the actual
class-sector vacua (`GenerationVacuumChoice`). It keeps a common wall action
independent of class and supplies exact generator/evolution observation. The
unbroken copies are degenerate and allow arbitrary class superpositions. Physical
generation/current identification and a breaking law are still required.

`CarrierRegisterModel` now gives a configuration-space witness for independent
spinor and payload labels. Two supplied banks use 32 Boolean registers in total;
one occupied register in each gives 256 encoded label pairs. The vacuum coordinate
embedding supplies an isometric 128-mode spinor–payload readout. The existing
native beta word and all packet permutations (including weak and colour) act on
separate banks and have exact all-state readout. Paper II owns the general
encoding, occupation conservation and operator-expression/evolution proofs.
The banks' allocation and preparation, full vacuum/current schedule, physical
reference/comparison integration and prices are still required. This is an
explicit representation candidate, not a selected physical state space.

The extension `CarrierRegisterVacuum` now supplies the full generator for every
momentum and detuning. Paper II's `RegisterHamiltonian` implements its entries as
occupation-dependent register hops and Hermitian completion; evolution conserves
total occupation and each payload bit on all sectors. The higher-occupation
completion and coherent hopping admission are specified choices. The actual
real-space split schedule, reference/current attachment and prices remain open.

The generic vacuum/encoding proofs are now canonical in Paper II's
`RegisterVacuum`; the Paper III modules retain their packet specializations and
compatibility names. Paper II also supplies `RegisterSplit`, `RegisterInteraction`,
`ChiralRegisterCurrent`, `RegisterReference` and `RegisterControl`: a shared finite
spatial register/current/record construction, with explicit memory, exact readout,
unitary evolution and a clock. Choosing and preparing that construction as the
physical model, attaching the packet charges and pricing its admitted gates
remain application/physical obligations.

`CarrierRegisterChirality` rules out imposing naive packet/wall or packet/Dirac-
chirality matching as a reducing sector of the complete vacuum Hamiltonian:
gapped states cross both matchings already at zero momentum and detuning. The
two matching masks agree on the zero-mode kernel, including entangled payload
amplitudes. A zero-mode chiral-current identification therefore does not by itself
identify every ambient state.

## Certified model values

### Native constants reporter

Build and run the reporter from this directory:

```sh
lake build pm-constants
.lake/build/bin/pm-constants
.lake/build/bin/pm-constants --json --digits 18
```

Lean compiles this to a native executable through its C backend. Running it needs
neither Python nor a separate C driver. The JSON output is also a small interface
for comparison programs; numeric bounds are strings to preserve their exact digits.

The initial catalog contains 14 entries: the impedance and admittance, partition
fractions, current colour-ledger coupling, current electron Yukawa, VEV ratio,
and the mass-scale quantities. `PMConstants.ConstantReport.catalog_sound` checks every
catalog endpoint against its named real-valued model formula. Building
`pm-constants` requires this certificate module, while the executable links only
the lightweight runtime modules. No noncomputable real expression is evaluated.

Exact fractions are printed where available; other entries have certified closed
bounds. Decimal formatting rounds those bounds outward using rational arithmetic,
with a general Lean enclosure theorem and executable formatting checks.
`--digits N` accepts 0–50 and changes formatting only: extra digits do not narrow
the proved intervals. These intervals enclose the model formulas; they are not
experimental uncertainties or a proof that the formulas follow from bare persistence.
The supplied electron-mass benchmark is labelled as an external input, including
its use by the GeV-valued outputs. The reporter does not infer an absolute scale.

`./check.sh` also checks the reporter's Lean certificates, formatting fixtures,
and an independent standard-library Python test of the compiled CLI and JSON.
The existing Python calculator remains available separately.

All interval endpoints are exact rationals in Lean.

| Quantity | Proved open interval |
| --- | --- |
| Geometric admittance α | (0.007297352562, 0.007297352563) |
| Current colour-ledger strong coupling | (0.11799520370, 0.11799520373) |
| Weak fraction | (0.2229053646, 0.2229053647) |
| Scalar self-coupling | (0.1294236602, 0.1294236603) |
| Current VEV-defined electron Yukawa | (0.00000293502845, 0.00000293502847) |

These are enclosures of the model formulas, not measurements. A mass input supplies the overall
unit; lattice dimensionless data do not supply an independent GeV scale.

## Module index

Generated from `PMConstants.lean`'s imports (in import order) and each module's docstring heading.

| Module | Subject |
| --- | --- |
| `General` | Aggregator for the substrate-independent general rules (capacity, encoding, matching, nesting, service) |
| `Partition` | Conditional arithmetic of the paper's partition rules, with no empirical identification. |
| `Depth` | Positivity of the stipulated gravity formula; Planck normalization and impedance ordering |
| `ReviewChecks` | Small review checks: tensor trace 8·3 = 24; idempotent projections have eigenvalues 0 and 1 |
| `Interface` | Exact versions of reversible remainder storage and a chosen real impedance |
| `Hypercharge` | Charge selection from specified conservation and coupling constraints |
| `Allocation` | What allocation equations select, and what finiteness does not select |
| `ElectroweakE8` | The proposed electroweak constants in E8 notation and their dependency graph |
| `Bulk` | Bulk propagation and the thermal floor |
| `Matching` | Exact interface matching is distinct from a small mismatch. Its unique |
| `CertifiedConstants` | Certified geometric values inherited from Paper I. Decimal endpoints are |
| `ReferenceFrames` | An internal reference and its resource cost |
| `SteadyAllocation` | Allocation from persistent finite queues |
| `RegulatoryBudget` | Clock credit and maximal uniform regulation |
| `ResourceSelection` | From specified resource processes to the allocation equations |
| `MatchedRegulation` | Exact matching selects a feasible gain with spare capacity |
| `FiniteService` | A finite scheduling witness and its quantization limit |
| `JointConstants` | Joint checks on the proposed electroweak constants |
| `GaugeSpectrum` | The neutral quadratic response and derived gauge mass relations |
| `ElectroweakBounds` | Certified consequences of the proposed formulas. `electronGeV` is the |
| `SurfaceBudget` | Apply the general reflected-load criterion to the stated Higgs/aperture |
| `WorkloadLedger` | Before selecting a coupling: what does the workload average count? |
| `TransitionLedger` | Primitive transition tolls versus composite operation costs |
| `AvailabilityAudit` | Availability measures and event semantics on the actual phase grid |
| `SelectedAvailability` | The availability mass is the selected law |
| `BalancedAvailability` | Collision semantics can give the aggregate payload count along each single |
| `ChannelDirectionLoad` | Quadratic direction loads of the actual minimal D4 glue-class vectors. |
| `PeriodicAllocation` | Allocation from cycle totals of the balanced collision model. |
| `ExclusionLawAudit` | Exact-update omission and conditional relational-load contracts |
| `LocalMaintenance` | A concrete local conservative transition and its measured cost |
| `RepairSpace` | Which changes could repair the joint electroweak residuals? |
| `ScaleConsistency` | One interface scale for all couplings? |
| `PersistentGain` | What persists at the scalar interface: maximal gain that pays for its own reflection |
| `ScaleResponse` | What a derived interface factor must contain |
| `StrongRunning` | The strong-coupling running test to the tau mass |
| `GaugeStiffness` | One rule for the gauge readouts: link stiffness proportional to refresh workload |
| `StiffnessIndices` | Per-sector normalization from the generation's channel content |
| `SectorLinks` | The inter-sector link is the scalar doublet |
| `ChiralAnomalies` | Gauge anomalies of the two-sector assignment |
| `BaryonNumber` | Baryon number from the axis ledger (`1/3` on colour, `0` on the lepton axis, matching `ReferenceAxis.bl`); native reversible gates preserve it, so a reversible update cannot create a baryon asymmetry (`no_asymmetry_from_reversible`) |
| `LinkMass` | W and Z masses from the inter-sector link |
| `LinkCustodial` | The opposite-sign interface term as custodial breaking of the link |
| `WMassTest` | The W mass as a parameter-free test of the clock ratio |
| `StrongLedgerTest` | Only one integer strong ledger survives |
| `CPPhases` | A real update fixes θ, and also forbids the measured CP violation |
| `HermitianMass` | Hermitian link masses: θ̄ = θ, with CP violation still allowed in mixing |
| `ColourCount` | What fixes the colour ledger: an exploration |
| `SectorExchange` | Sector exchange makes the link mass Hermitian; one doublet's phase cancels in θ̄ |
| `ColourChannels` | Colour refreshes the coloured channels: `L₃ = 12η` |
| `ResourceLedger` | Shared versus per-channel resources: one rule for the weak and colour ledgers |
| `GaugeLedgers` | One rule, one table: all three gauge ledgers |
| `MinimalRefresh` | Compatibility names; generic schedule proofs now live in Paper II. |
| `RequirementTable` | The requirement table from the representation and the forced charges |
| `StrongLedgerBounds` | Certified enclosures for the colour-ledger strong coupling |
| `ContentWeight` | Conditional comparison of common stored-content weights |
| `EventStiffness` | Gauge stiffness from Paper II's event law |
| `GaugeGroupFactor` | Gauge group factors from the event-priced D₄ action |
| `ReferenceStiffness` | Reference stiffness from the event-priced D₄ continuum limit |
| `ChainCouplings` | All three gauge couplings from the event-priced D₄ chain |
| `ScalarNormalization` | Scalar normalization from the event-priced D₄ chain |
| `RunningResponseLink` | Matter running coefficients from Paper II's spin and orbital response |
| `RunningDerived` | Paper III's running tests on derived coefficients |
| `WeakSpectrumLinks` | Paper II's W-exchange vertex and exact wall spectrum, applied to Paper III |
| `VevEntry` | How the VEV enters the wall masses: the inter-wall link is excluded |
| `SectorObligations` | Sector obligations from the record bound and the reference repair |
| `ReadScale` | One rule for both matching scales |
| `OnShell` | Why an executing mode is read at its mass |
| `LinkFromEvents` | The W/Z mass form is the leading event-law link response |
| `ScalarSector` | The scalar sector against data without the predicted VEV |
| `FermionMassLaw` | How the link sets fermion masses: the Higgs couplings decide |
| `VevAccounting` | Which subtraction the VEV formula can persist with |
| `VevPremises` | The VEV's two structural premises, made sharp |
| `DepthEvents` | The gravitational attenuation from the event law: why `α`, and why `α^{43/2}` |
| `CarrierRepresentation` | The channel representation from Paper I's carriers |
| `Generations` | Three unordered distinct-class pair types under the vector-faithful packet contract |
| `GenerationEncoding` | Exhaustive pair classification, exact binary encoding and 48-versus-24 linear capacity bound |
| `GenerationHistory` | Companion-carrier representation, coherent isometry and native root-word preservation |
| `GenerationWalls` | Two-wall representation, balanced incidence classification and wall-exchange test |
| `GenerationVacuumChoice` | Native class-sector vacuum as an alternative readout contract; no selected masses or generations |
| `CarrierPhaseComparison` | Exact comparison on packet involutions, with controlled phases and supplied spatial cells |
| `FloorNeutrino` | Bare thermal tower and common-scale splitting obstruction |
| `BetaUniversality` | The rank rule for the beta coefficient fails its own universality test |
| `GravityAccounting` | Which channel count the gravitational coupling can persist with |
| `ScalarAccounting` | The scalar ledger picks the same channel accounting |
| `ScalarBudget` | The scalar ledger's budget is the integer 3 |
| `BoundaryStorage` | The gravity residual's boundary-storage term |
| `CarrierActions` | Actual finite carrier operations behind two representation columns. |
| `CarrierImplementation` | A finite register realization of the carrier actions. This is a local |
| `CarrierPhaseResponse` | Hypercharge-sensitive carrier readout. The existing charge/axis premises |
| `CarrierSwapSchedule` | Concrete reversible two-field implementations of the carrier gates. |
| `ColourRouting` | Paper V's internal-address interpretation, as a precise finite quotient. |
| `ColourRefreshCadence` | Capability, requests and refresh cadence are distinct operational contracts. |
| `ColourPhaseMaintenance` | Phase-response constraints on maintenance weights. Three balanced diagonal |
| `ColourGeometricLoad` | Actual carrier quadratic load restricted to colour, under the existing |
| `CurrentConstants` | Public snapshot of the current manuscript formulas. The old dressed Yukawa |
| `LinkSpectralResponse` | Discharge spectral data from the actual W/Z link response. The spectral |
| `LinkEvolution` | Paper III compatibility names and the W/Z specialization. |
| `PacketGaugeActions` | Common unitary weak and colour actions on the actual packet, with the |
| `PacketTraceForm` | Exact quadratic trace form of the common packet representation. These |
| `MeanTraceResponse` | Controlled quadratic response of uniform comparison on a finite Hermitian |
| `GaugeTraceNormalization` | Consequences of the actual packet trace indices for the ledger reading. |
| `SelectedColourLoad` | Close the conditional selection-to-colour chain for an arbitrary positive |
| `GaugePersistenceChoice` | What persistence selects once work has an operational meaning. |
| `ReadoutAccounting` | The W mass decides how the gauge ledgers enter the coupling law |
| `GeneratorNormalization` | Which generator normalization the gauge ledgers price |
| `ReferenceCharge` | The common reference carrier fixes the charge-unit normalization |
| `SharedReference` | One reserved cell, one reference: the weak and hypercharge refreshes share it |
| `ColourReference` | Colour reads the payload: the ledger `12η` |
| `ReferenceAnchor` | What the lepton-doublet reference supplies elsewhere |
| `ReferenceStabilizer` | What the lepton-doublet reference leaves unbroken |
| `ReferenceDirections` | How many directions the electroweak actions can move the reference |
| `RegulatoryMaximin` | Equal regulatory gain from maximin, and the count 23 from the measured coupling |
| `ReferenceRestoration` | Three closures for the scalar ledger |
| `ReferenceLink` | The scalar link carries the reference's charge |
| `ReferenceMasses` | What the reference gives the gauge bosons |
| `ReferenceEconomy` | Economy places the references; unbroken colour picks the lepton doublet |
| `PersistenceClosures` | Closures by persistence |
| `ReferenceAxis` | The reference singles out the lepton axis |
| `RequirementRows` | Which frame rows the electroweak refreshes cover |
| `RequirementComplement` | The rest of the requirement table: complement and per-channel routing |
| `TableConsequences` | What the derived requirement table gives end to end |
| `ReadoutScales` | Where each readout is matched |
| `RunningLinks` | Paper III's running coefficients come from Paper II |
| `MatterRunning` | Paper II's dynamics applied to Paper III's derived content |
| `HyperScope` | Which hypercharge scope the W mass allows |
| `PreparationSelection` | The uniform preparation as an instance of law selection |
| `ScalePairing` | Which electric coupling the colour formula pairs with `α_s(M_Z)` |
| `StableReadout` | Why the colour formula pairs `α(0)` with `α_s(M_Z)` |
| `RegulatoryLabels` | The 23 regulatory labels are the coordinates of a link hop |
| `VevCorrections` | What the Fermi window says about the VEV corrections |
| `NeutralCurrent` | The photon and Z couplings from the reference's mass form |
| `RepairBudget` | The scalar budget from one exact repair of the reference |
| `BudgetReadout` | What the scalar budget reads from a repair |
| `CoherentBudget` | The scalar budget with the coherent restorer as the repair |
| `TangentResponse` | The real drift family's response totals 3 |
| `WalkTrials` | The finite walk protocol read against the scalar ledger |
| `GaugeWalkBudget` | The scalar's repair with the weak doublet on its own payload index |
| `NoiseShare` | Why the VEV's noise divisor is `3`, not `4` |
| `VacuumModulus` | θ = 0 is unique under the modulus too, once the trivial sector counts |
| `WallParityExchange` | θ̄ = θ from the wall exchange that is a symmetry |
| `ChannelOccupancy` | The sixteen channels are one observed generation, with no slot to spare |
| `ReflectionCharge` | The reflection charge rate `c` |
| `VevReadout` | The VEV corrections as one exact repair, read out once |
| `VevEvent` | The VEV is read from an event, and events happen only on spatial hops |
| `ReferenceWalkParity` | Compatibility names: the general dynamics proofs now live in Paper II. |
| `CarrierReadoutOrbits` | Classify basis-preparation weights invariant under the actual weak flip |
| `WeightedReadoutResponse` | The event/response map for supplied nonnegative preparation or work weights. |
| `GaugeReadoutWeights` | Response indices for every type-invariant incoherent basis preparation. |
| `LinkPreparation` | Stationary diagonal preparation under inter-type transfer. The generator, |
| `TypedRepairWork` | Price supplied type-dependent integer repairs using the actual comparison |
| `PrimitiveReadoutSymmetry` | A paired carrier-reflection action tests the six-type preparation freedom. |
| `CoherentComparisonRepair` | Compatibility names: the general dynamics proofs now live in Paper II. |
| `ControllerHamiltonian` | Compatibility names: the general dynamics proofs now live in Paper II. |
| `ReferenceMaintenance` | Compatibility names; generic reversible tasks now live in Paper II. |
| `ReferenceMaintenanceLedger` | Executable conditional ledgers and a partition countermodel |
| `SectorCapabilities` | Capabilities of the actual carrier operations |
| `GenerationEncoding` | Three packet types, retained labels and finite encoding capacity |
| `GenerationHistory` | Companion-carrier encoding and generation-preserving root words |
| `GenerationWalls` | Wall-retaining packet encodings and the wall-exchange constraint |
| `GenerationVacuumChoice` | Existing class-sector vacua and unbroken class degeneracy |
| `CarrierPhaseComparison` | Marker-free comparison on the actual packet permutations |
| `PMConstantsProof` | Build-time certificates for the native constants reporter |
| `CarrierRegisterModel` | Independent occupied banks for actual vacuum and packet labels |
| `CarrierRegisterVacuum` | Full native vacuum generator on those configuration banks |
| `CarrierRegisterChirality` | Full-state matching obstructions and zero-kernel agreement |
