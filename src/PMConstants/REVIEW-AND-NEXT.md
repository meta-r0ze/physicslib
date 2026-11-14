# PMConstants — open work

- **Strong CP.** Bring the external unit-transfer certificate into Lean: verify invertibility and the change from 162 to 163 filled modes for the two Wilson kernels. The anomaly relation is derived (`PMAction.WallTransfer`, `FermionFlip`); the selection argument admits the θ-vacua as least-cost candidates. [Certificate](../../tools/unit_transfer_certificate.py) · [Selection theorem](ThetaBarSelection.lean)
- **Running couplings.** Bound the finite-spacing errors in the polarization integral over the window: replace the continuum propagator and vertex by the substrate's (`symbol_gap`, `vertex_gap`) inside `PMAction.PolarizationRemainder.polarization_window`, whose continuum `q`-expansion remainder is already bounded (`500|q|³/μ · 2π² ln(M/μ)`). [Polarization remainder](../PMAction/PolarizationRemainder.lean) · [Leading log](../PMAction/LeadingLog.lean)
- **Audit: two readings of the two `D₄` summands.** `WeakLocality`'s docstring reads `E₈ = D₄ ⊕ D₄`
  as "spacetime and internal" (one summand each); `PMAction.DomainWall` and the 38 modules built on
  it read the two summands as the two walls, copies of one lattice with opposite chirality
  (`GenerationWalls`, `WallExchange`, the flavour sector). These cannot both hold. Check whether
  `WeakLocality`'s argument (weak's events are internal, so they move no site) needs the
  spacetime/internal reading or only `FactorRepair`'s factor structure (one root event acts in one
  gauge factor); if the latter, reword the docstring. If it needs the former, the conflict with the
  wall reading is real and has to be settled before either is used further.

