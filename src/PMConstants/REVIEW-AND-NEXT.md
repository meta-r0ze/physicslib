# PMConstants — open work

What is still open, so it can be prioritized. Finished work is documented in the module
docstrings and [`OVERVIEW.md`](OVERVIEW.md); `CurrentConstants.current_snapshot` has the current
values. A certified value follows from its stated formula and premises; "open" below means a
premise not yet derived from persistence, geometry or constraints.

## Shared blockers, in priority order

1. **The physical controller and register implementation.** Which E8 root words realize the
   comparison gates, clean-cell allocation, and the clock/spatial/wire requirements
   (PMAction REVIEW B.2, the microscopic hop). The admission rule is stated
   (`PMAction.Admission`) and the controller's selection is fixed (`ControllerLedger`, typed
   repairs `(2,1,1,1,1)`); the implementation is not. Blocks: weak fraction, VEV, G_F, m_H, η
   maintenance.
2. **The preparation contract.** Identifying the carrier preparation with the survival model
   (`PreparationSelection`) is the same input as Machine's prepared initial reference
   (`PrimitiveRecordBoundary.cannot_prepare`). Blocks: η, weak fraction.
3. **Update and propagation dynamics.** Generations, running thresholds, the gravity loop and
   neutrino mixing. Mostly companion-paper work (Papers IV–VI).
4. **Imported or cited inputs.** The chiral-anomaly relation, Lüscher's lattice charge on PM's
   region, a charge-1 history (strong CP). Standard results; formalizing them is heavy and low
   priority.

## Open, by constant

| Constant | Status | Still open |
| --- | --- | --- |
| D, Δ, ν, σ, χ; α | Forced given Paper I's postulates | Paper I's postulates themselves (`PMSubstrate` REVIEW). |
| η = 171/172 | One reserved tone (frame synchronization) is needed and optimal (`ReferenceFrames`, `no_total_origin_readout`, `inband_optimal_iff`); no cell-width premise | Maintenance is required (`ReferenceAxis.skipped_maintenance_fails`) and its task model exists: reversible restoration with a retained record, each required job visited once at minimal cost (`PMAction.Machine.ReferenceMaintenance`). Clean records are not renewable inside that model, so their supply is the preparation contract (blocker 2); that is the only open part. |
| Weak fraction 1849/8295 | End to end (`TableConsequences.end_to_end`); charge-unit normalization from the lepton-doublet reference (`ReferenceCharge`, `ReferenceEconomy`) | The controller implementation (blocker 1). Premises: one reserved cell per reference type; both electroweak refreshes read it. |
| α_s | Formula, colour normalization (`ColourNormalization`), twelve reads (`SectorObligations`), read scale (`ReadScale`) | The coupling on the hadron carrier cube (PMAction REVIEW A.3). (Colour's required resources are now derived: `ColourReference.coloured_iff_triplet`.) |
| g_W, g_Y, g_3 | From the D₄ gauge action and summed charge-unit reads (`ChainCouplings`) | Cubic link consistency reduces to exact subdivision: an update that composes under subdivision with a differentiable response obeys the transport ODE (`PMAction.CompositionalTransport.ode_of_composes`), and transport links are cubically consistent (`ParallelTransport.transport_consistent`). Proved for the native packet subsystem (`NativePacketUpdate.native_composes`, `packet_contracts`, C² controls); open: that the full gauge sectors' updates compose exactly. The physical scale convention. |
| λ = 128/989 | Persistent gain within `1.4·10⁻⁹` below 128/989 (`ReflectionCharge.gain_at_three`) | The unit (Closure's minimal repair, as `NetCost`'s toll), the once-per-cycle clock resync (skipped maintenance fails, Economy; the same single sync that fixes η) and the same-kind reflected repair (`budget_readout` covers every exact repair) are now linked in `BudgetReadout` and `ReflectionCharge`. The reflected load being the complete repair's fraction follows from equal gain (`ReflectionCharge.labels_sum_to_whole`). Nothing open beyond the persistence premises themselves. |
| Scalar Toll, μ² | `T = 2λ`, `μ² = λv²`; `Z_φ` from scalar transport (`ScalarNormalization`) | Nothing beyond λ and v. How the budget is spent over time (budget dynamics) does not enter the values. |
| VEV v | Factorized and composed (`VevLedger`, `VevClosure`); wire share, linear form and noise divisor derived | The controller implementation (blocker 1). `m_e` is the mass unit by proof (`PMSubstrate.SIUnits`). |
| y_e | Closure `√2 m_e/v` | Nothing: y_e is the closure of the VEV in `m_e` units, not an independent prediction. |
| G_F | W exchange on the reference (`MatterRunning.fermi_from_reference`) | Same as the VEV. |
| m_H | `m_H² = 2λv²`; `Z_φ` derived (`ScalarNormalization`, `ScalarVevLink`) | Response corrections. (128/989 is a ratio of frame-independent readouts and counts, unchanged by the rescaling `Φ ↦ √Z_φ Φ` (`BudgetReadout.budget_normalization_free`), so it is the canonical quartic `m_H²/(2v²)`.) |
| W/Z masses | `m_W² = (3/344)v_sub²`, ρ = 1, `Δr_sub = 5α/(1+5α)` in the Z-anchor window (`InterfaceResponseLaw`) | Beyond the VEV, nothing: `Δα`, `m_t` and the remainder are comparison diagnostics, and a measured `m_Z` tests the W relation. |
| Hypercharges / generations | Charges up to the `e`/`ν` labeling (`ReferenceLink`); three glue-class pair types; one binary wall tag suffices (`GenerationEncoding`) | Triality is settled (every nontrivial class is carried to the vector class keeping the roots, `ChannelSymmetry.class_to_vector`; all classes admitted); the lepton axis is the reserved tone cell's carrier axis (`ReferenceAxis`, `one_axis`); the sign is the doublet index because it is the only move keeping a carrier's axis (`CarrierActions.same_axis_iff`); the weak refresh is chiral: the minimal sector-uniform sign action moving the reference acts on the reference's sector only (`CarrierActions.weak_chiral`), and "left" names that sector (premise: refreshes act uniformly on a sector). The physical generation classification (accessibility, current and update of the tag); a vector-faithful readout for equal-class packets. |
| Strong CP θ̄ | θ̄ = 0 for any invertible masses (`ThetaBarSelection`, `WindingWeights`) | Blocker 4. Premise: the vacuum phase is a variable the selection acts on. |
| Running | b₃, b₂, b_Y from derived content; all spin terms derived in Paper II | The physical controls and the matter-fluctuation identification; smooth C² controls for the native packet. (Thresholds are supplied: the E8 quark masses with `ScaleResponse`'s species-additive threshold law, `StrongRunning.flavour_order`, `RunningLinks.threshold_coefficients`.) |
| Jarlskog J | Matrix value from Paper IV | Nothing here; the CKM inputs are `PMFlavor`'s. |
| α_G | `α^{43/2}` from the event law and loop; handoff probability `α` from admittance (`HandoffAdmittance`) | That a gravitational handoff sees the node's admittance: argued from Closure (a node cannot price a crossing by what it carries, `HandoffAdmittance`), not proved. (The gravity loop is a clock loop: at one handoff per tick, a loop that returns to its clock phase has at least `Δ` handoffs, `DepthEvents.closed_loop_handoffs`, attained by the clock cycle.) |
| Planck scale | Unity scale `m_e/√α_G` | Physical `α_G` normalization. |
| Thermal floor | Proposed floor ≈ 9.21 meV | Propagation depth, mode population, coupling, and its reading as a density. |
| Neutrinos | The bare tower is excluded (gap ratios 1:1849:1850) | A derived propagation/mixing Hamiltonian (Papers V/VI). |

## Candidates (explain a selection; not independent derivations)

* `RootRepairRule`, `SectorRepair`: one root event per non-abelian factor, at least one per
  gauge-charged object. Reproduces the unique least-cost typed repair `(2,1,1,1,1)` that gives
  `clockRatio`, and makes the gauge and scalar sectors share one repair length (fermion counts are
  field rescalings). Found post hoc.
* `HandoffAdmittance`: transmission linear in admittance with a unit channel open (Landauer).

## Failure tests that narrow the controller

Stationary diagonal preparations with nonzero Q–u/Q–d hops miss the raw mixing; coherences fail
in the pairwise zero-onsite family; uniform or paired-reflection-invariant work does not recover
both raw-ledger readouts; a common repair length misses `clockRatio`
(`TypedRepairWork.common_repair_cannot_match`). Effective-stiffness ledgers, state-dependent
protocol work and more general dynamics remain open routes.

## Entry points

- Values and bounds: `CurrentConstants`, `CertifiedConstants`, `StrongLedgerBounds`.
- Controller and work: `ControllerLedger`, `TypedRepairWork`, `RootRepairRule`, `SectorRepair`.
- Readout: `GaugeReadoutWeights`, `WeightedReadoutResponse`, `ReferenceCharge`, `ReferenceFrames`.
- Scalar and scale: `ScalarLedger`, `ReflectionCharge`, `VevLedger`, `VevReadout`.
- Update and propagation: `ThetaBarSelection`, `WindingWeights`, `DepthEvents`, `HandoffAdmittance`.

See [`README.md`](README.md) for build instructions.
