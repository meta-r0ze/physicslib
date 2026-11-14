# PMConstants — open work

- **Strong CP premise.** `HermitianMass.thetaBar_eq_theta` assumes a Hermitian inter-wall link, but
  within one convention the equal-class crossing is one-directional and not Hermitian
  (`GenerationParity`). Its determinant is the product of the three crossing amplitudes (cyclic
  support); show it is real (the crossing is `PMAction.DomainWall`'s fixed real hop, the same for every
  class) and that the composite diagonal masses (`GenerationMass`) keep `arg det M = 0`, or record
  that `θ̄ = 0` needs a different premise.
- **Strong CP.** Bring the external unit-transfer certificate into Lean: verify invertibility and the change from 162 to 163 filled modes for the two Wilson kernels. The anomaly relation is derived (`PMAction.WallTransfer`, `FermionFlip`); the selection argument admits the θ-vacua as least-cost candidates. [Certificate](../../tools/unit_transfer_certificate.py) · [Selection theorem](ThetaBarSelection.lean)
- **Running couplings.** Bound the finite-spacing errors in the polarization integral over the window: replace the continuum propagator and vertex by the substrate's (`symbol_gap`, `vertex_gap`) inside `PMAction.PolarizationRemainder.polarization_window`, whose continuum `q`-expansion remainder is already bounded (`500|q|³/μ · 2π² ln(M/μ)`). [Polarization remainder](../PMAction/PolarizationRemainder.lean) · [Leading log](../PMAction/LeadingLog.lean)
- **Dressing outlets.** `PMFlavor.DressingEvent.event_law_spatial` works on `Fin 4` labels (no position
  or hop), so the outlet count needs no site move. Open: whether the actual CKM loss realizes that
  event law (zero rate on the time label, equal rate-weighted shares on the three spatial labels) and
  the row-to-outlet identification. Carrier space and the lattice share axis labels only; a carrier
  label change is not a site move (`WeakLocality`, `hL`).
