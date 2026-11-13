# PMConstants — open work

What is still open, so it can be prioritized. Finished work is documented in the module
docstrings and [`OVERVIEW.md`](OVERVIEW.md); `CurrentConstants.current_snapshot` has the current
values. A certified value follows from its stated formula and premises; "open" below means a
premise not yet derived from persistence, geometry or constraints.

## Shared blockers, in priority order

1. **Imported or cited inputs.** Lüscher's lattice charge on PM's region (its identification with
   the substrate's wall-transfer count) and a charge-1 history (strong CP). The chiral-anomaly
   relation itself is derived on the substrate (`PMAction.WallTransfer`, `PMAction.FermionFlip`).

## Open, by constant

Rows with nothing open (η, λ, scalar Toll and μ², y_e, W/Z beyond the VEV, Jarlskog J, g_W, g_Y,
g_3, and α_G beyond the Closure premise) are left out; their modules record how they close.

| Constant | Still open |
| --- | --- |
| Weak fraction 1849/8295 | Premise: a sector refreshes a resource only where its own events reach or restore something, the abelian phase riding on events that occur (the reading of `PMAction.FactorRepair`). The derivation from it is `WeakConfinement.weak_fraction`. |
| VEV v, G_F | The VEV's correction factors (`VevPremises`). (The electron's maintenance is one repair: derived, `RootRepairRule.electron_one_event`.) |
| m_H | Response corrections, which are below current precision: the tree value `125.2692638–125.2692640` GeV is `+0.6σ` from PDG `125.20 ± 0.11`. |
| Hypercharges / generations | The tag is the wall, so its dynamics is the inter-wall link `Y` (`WallExchange`, `WallSeesaw`: light masses `δ²/σᵢ(Y)`); its entries belong to `PMFlavor`, which builds on this folder. Premise: refreshes act uniformly on a sector (`CarrierActions.weak_chiral`). |
| Strong CP θ̄ | Blocker 1. Premise: the θ-vacua are vacuum candidates, selected by least cost like the substrate's own vacuum (`PMSubstrate.Vacuum.vacuum_selects`). |
| Running | The matter-fluctuation identification. |

## Candidates (explain a selection; not independent derivations)

* `HandoffAdmittance`: transmission linear in admittance with a unit channel open (Landauer),
  and the Closure reading for the gravitational handoff.

## Entry points

- Values and bounds: `CurrentConstants`, `CertifiedConstants`, `StrongLedgerBounds`.
- Controller and weak fraction: `RootRepairRule`, `SectorRepair`, `WeakLocality`, `WeakConfinement` (the settled controller is summarized in [`OVERVIEW.md`](OVERVIEW.md)).
- Readout and preparation: `ReferenceCharge`, `ReferenceFrames`, `PreparationSelection`.
- Scalar and scale: `ScalarLedger`, `BudgetReadout`, `ReflectionCharge`, `VevLedger`.
- Update and propagation: `ThetaBarSelection`, `WindingWeights`, `DepthEvents`, `HandoffAdmittance`.

See [`README.md`](README.md) for build instructions.
