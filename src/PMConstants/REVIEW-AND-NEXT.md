# PMConstants — open work

What is still open, so it can be prioritized. Finished work is documented in the module
docstrings and [`OVERVIEW.md`](OVERVIEW.md); `CurrentConstants.current_snapshot` has the current
values. A certified value follows from its stated formula and premises; "open" below means a
premise not yet derived from persistence, geometry or constraints.

## Shared blockers, in priority order

1. **The physical controller and register implementation.** Which E8 root words realize the
   comparison gates, clean-cell allocation, and the clock/spatial/wire requirements
   (PMAction REVIEW B.2, the microscopic hop). The admission rule, the controller's selection
   (`ControllerLedger`, typed repairs `(2,1,1,1,1)`) and the gate's coherent state
   (`PMAction.CoherentPreparation`) are settled; the implementation is not. Blocks: weak
   fraction, VEV, G_F, m_H.
2. **Update and propagation dynamics.** The generation tag's dynamics, the physical running
   controls and neutrino mixing. Mostly companion-paper work (Papers IV–VI).
3. **Imported or cited inputs.** The chiral-anomaly relation, Lüscher's lattice charge on PM's
   region, a charge-1 history (strong CP). Standard results; formalizing them is heavy and low
   priority.

## Open, by constant

Rows with nothing open (η, λ, scalar Toll and μ², y_e, W/Z beyond the VEV, Jarlskog J) are left
out; their modules record how they close.

| Constant | Still open |
| --- | --- |
| D, Δ, ν, σ, χ; α | Paper I's postulates themselves (`PMSubstrate` REVIEW). |
| Weak fraction 1849/8295 | The controller implementation (blocker 1). Premises: one reserved cell per reference type; both electroweak refreshes read it. |
| VEV v, G_F | The controller implementation (blocker 1). |
| m_H | Response corrections. |
| α_s | The coupling on the hadron carrier cube (PMAction REVIEW A.3). |
| g_W, g_Y, g_3 | That the full gauge sectors' updates compose exactly under subdivision (proved for the native packet subsystem; this is what cubic link consistency reduces to). The physical scale convention. |
| Hypercharges / generations | The generation tag's dynamics: accessibility, current and update (blocker 2). Premise: refreshes act uniformly on a sector (`CarrierActions.weak_chiral`). |
| Strong CP θ̄ | Blocker 3. Premise: the vacuum phase is a variable the selection acts on. |
| Running | The physical controls and the matter-fluctuation identification; smooth C² controls for the native packet. |
| α_G, Planck scale | That a gravitational handoff sees the node's admittance: argued from Closure (`HandoffAdmittance`), not proved. |
| Thermal floor | Propagation depth, mode population, coupling, and its reading as a density. |
| Neutrinos | A derived propagation/mixing Hamiltonian (Papers V/VI). |

## Candidates (explain a selection; not independent derivations)

* `RootRepairRule`, `SectorRepair`: one root event per non-abelian factor, at least one per
  gauge-charged object. Reproduces the unique least-cost typed repair `(2,1,1,1,1)` that gives
  `clockRatio`, and makes the gauge and scalar sectors share one repair length. Found post hoc.
* `HandoffAdmittance`: transmission linear in admittance with a unit channel open (Landauer),
  and the Closure reading for the gravitational handoff.

## Failure tests that narrow the controller

Stationary diagonal preparations with nonzero Q–u/Q–d hops miss the raw mixing; coherences fail
in the pairwise zero-onsite family; uniform or paired-reflection-invariant work does not recover
both raw-ledger readouts; a common repair length misses `clockRatio`
(`TypedRepairWork.common_repair_cannot_match`). Effective-stiffness ledgers, state-dependent
protocol work and more general dynamics remain open routes.

## Entry points

- Values and bounds: `CurrentConstants`, `CertifiedConstants`, `StrongLedgerBounds`.
- Controller and work: `ControllerLedger`, `TypedRepairWork`, `RootRepairRule`, `SectorRepair`.
- Readout and preparation: `ReferenceCharge`, `ReferenceFrames`, `PreparationSelection`.
- Scalar and scale: `ScalarLedger`, `BudgetReadout`, `ReflectionCharge`, `VevLedger`.
- Update and propagation: `ThetaBarSelection`, `WindingWeights`, `DepthEvents`, `HandoffAdmittance`.

See [`README.md`](README.md) for build instructions.
