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
   (`PMAction.CoherentPreparation`) are settled. Root words so far: the coherent step is one root
   reflection at quarter period (`Machine.CarrierRootGate`), and a within-tick axis step is the
   equal-weight sum of the four in-slice two-root words (`Machine.AxisHop`, `Machine.SliceHop`).
   Still open: the full gate sequence and its register/clean-cell layout. Blocks: weak fraction,
   VEV, G_F, m_H.
2. **Flavour entries.** The flavour link `Y` that carries the generation tag (`PMFlavor`,
   Paper IV). (The native packet's C² controls are no longer a blocker: they follow from the
   substrate's links for every finite `D₄` configuration, `PMAction.Machine.D4EdgeSeparation`.)
3. **Imported or cited inputs.** The chiral-anomaly relation, Lüscher's lattice charge on PM's
   region, a charge-1 history (strong CP). Standard results; formalizing them is heavy and low
   priority.

## Open, by constant

Rows with nothing open (η, λ, scalar Toll and μ², y_e, W/Z beyond the VEV, Jarlskog J, g_W, g_Y,
g_3, and α_G beyond the Closure premise) are left out; their modules record how they close.

| Constant | Still open |
| --- | --- |
| Weak fraction 1849/8295 | The controller implementation (blocker 1). (Its two reference premises are derived: one carrier state per reserved cell, `ReferenceEconomy.cell_inj_of_content`; both electroweak refreshes read the reserved cell, `reads_reserved`.) |
| VEV v, G_F | The controller implementation (blocker 1). |
| m_H | Response corrections, which are below current precision: the tree value `125.2692638–125.2692640` GeV is `+0.6σ` from PDG `125.20 ± 0.11`. |
| α_s | The coupling on the hadron carrier cube (PMAction REVIEW A.3). |
| Hypercharges / generations | The tag is the wall, so its dynamics is the inter-wall link `Y` (`WallExchange`, `WallSeesaw`: light masses `δ²/σᵢ(Y)`); its entries are the flavour sector's (`PMFlavor`). Premise: refreshes act uniformly on a sector (`CarrierActions.weak_chiral`). |
| Strong CP θ̄ | Blocker 3. Premise: the θ-vacua are vacuum candidates, selected by least cost like the substrate's own vacuum (`PMSubstrate.Vacuum.vacuum_selects`). |
| Running | The matter-fluctuation identification. (Its C² controls follow from the substrate, `PMAction.Machine.D4EdgeSeparation`.) |
| Thermal floor | Out of scope here (Papers V/VI): propagation depth, mode population and its reading as a density. |
| Neutrinos | Out of scope here (Papers V/VI): a derived propagation/mixing Hamiltonian. |

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
