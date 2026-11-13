# PMConstants — open work

What is still open, so it can be prioritized. Finished work is documented in the module
docstrings and [`OVERVIEW.md`](OVERVIEW.md); `CurrentConstants.current_snapshot` has the current
values. A certified value follows from its stated formula and premises; "open" below means a
premise not yet derived from persistence, geometry or constraints.

## Shared blockers, in priority order

None. The unit-transfer history that strong CP needed is certified outside Lean (see its row).

## Open, by constant

Rows with nothing open (the weak fraction, η, λ, scalar Toll and μ², y_e, W/Z beyond the VEV, Jarlskog J, g_W, g_Y,
g_3, and α_G beyond the Closure premise) are left out; their modules record how they close.

| Constant | Still open |
| --- | --- |
| VEV v, G_F | The VEV's correction factors (`VevPremises`). (The electron's maintenance is one repair: derived, `RootRepairRule.electron_one_event`.) |
| m_H | Response corrections, which are below current precision: the tree value `125.2692638–125.2692640` GeV is `+0.6σ` from PDG `125.20 ± 0.11`. |
| Hypercharges / generations | The tag is the wall, so its dynamics is the inter-wall link `Y` (`WallExchange`, `WallSeesaw`: light masses `δ²/σᵢ(Y)`); its entries belong to `PMFlavor`, which builds on this folder. Premise: refreshes act uniformly on a sector (`CarrierActions.weak_chiral`). |
| Strong CP θ̄ | The unit-transfer history is certified outside Lean (`tools/unit_transfer_certificate.py`: on the `3⁴` torus the Hermitian Wilson kernel at the Wilson point has `162` filled modes for the trivial history and `163` for a unit-flux one, both invertible, by ball-arithmetic congruence and Sylvester's law); a Lean proof is a certified-numerics task like `PMAction` A.1. Premise: the θ-vacua are vacuum candidates, selected by least cost like the substrate's own vacuum (`PMSubstrate.Vacuum.vacuum_selects`). |
| Running | Mechanical: the integrated remainder of the polarization integral over the window (the `q³` term of `inv_expand` and the `O(a²)` propagator and vertex corrections, `symbol_gap`, `vertex_gap`), as `LeadingLog.shell_lattice` does for the contact. Derived: the orbital `−1/3` as the D₄ moment average (`PMAction.PolarizationAverage.orbital_third`), equal to the continuum shell's (`PMAction.ShellMoments.shell_eq_root_average`, `shell_orbital`); the shell unit (`LeadingLog.leading_log`) and `running_unit`'s `2π`; the matter operators (`Machine.MatterContinuum`). |

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
