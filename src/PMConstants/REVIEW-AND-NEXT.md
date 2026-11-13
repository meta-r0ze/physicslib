# PMConstants — open work

## Open, by constant


| Constant | Still open |
| --- | --- |
| VEV v, G_F | The VEV's correction factors (`VevPremises`). |
| m_H | Response corrections, which are below current precision: the tree value `125.2692638–125.2692640` GeV is `+0.6σ` from PDG `125.20 ± 0.11`. |
| Hypercharges / generations | The tag is the wall, so its dynamics is the inter-wall link `Y` (`WallExchange`, `WallSeesaw`: light masses `δ²/σᵢ(Y)`); its entries belong to `PMFlavor`, which builds on this folder. Premise: refreshes act uniformly on a sector (`CarrierActions.weak_chiral`). |
| Strong CP θ̄ | The unit-transfer history is certified outside Lean (`tools/unit_transfer_certificate.py`: on the `3⁴` torus the Hermitian Wilson kernel at the Wilson point has `162` filled modes for the trivial history and `163` for a unit-flux one, both invertible, by ball-arithmetic congruence and Sylvester's law); a Lean proof is a certified-numerics task like `PMAction` A.1. Premise: the θ-vacua are vacuum candidates, selected by least cost like the substrate's own vacuum (`PMSubstrate.Vacuum.vacuum_selects`). |
| Running | Mechanical: the integrated remainder of the polarization integral over the window (the `q³` term of `inv_expand` and the `O(a²)` propagator and vertex corrections, `symbol_gap`, `vertex_gap`), as `LeadingLog.shell_lattice` does for the contact. |

## Candidates (explain a selection; not independent derivations)

* `HandoffAdmittance`: transmission linear in admittance with a unit channel open (Landauer),
  and the Closure reading for the gravitational handoff.
