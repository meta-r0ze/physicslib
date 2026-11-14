# PMConstants — open work

- **Strong CP.** Bring the external unit-transfer certificate into Lean: verify invertibility and the change from 162 to 163 filled modes for the two Wilson kernels. The anomaly relation is derived (`PMAction.WallTransfer`, `FermionFlip`); the selection argument admits the θ-vacua as least-cost candidates. [Certificate](../../tools/unit_transfer_certificate.py) · [Selection theorem](ThetaBarSelection.lean)
- **Running couplings.** Bound the finite-spacing errors in the polarization integral over the window: replace the continuum propagator and vertex by the substrate's (`symbol_gap`, `vertex_gap`) inside `PMAction.PolarizationRemainder.polarization_window`, whose continuum `q`-expansion remainder is already bounded (`500|q|³/μ · 2π² ln(M/μ)`). [Polarization remainder](../PMAction/PolarizationRemainder.lean) · [Leading log](../PMAction/LeadingLog.lean)
- **Dressing outlets.** `PMFlavor.DressingEvent.event_law_spatial` works on `Fin 4` labels (no position
  or hop), so the outlet count needs no site move. Open: whether the actual CKM loss realizes that
  event law (zero rate on the time label, equal rate-weighted shares on the three spatial labels) and
  the row-to-outlet identification. Carrier space and the lattice share axis labels only; a carrier
  label change is not a site move (`WeakLocality`, `hL`).
