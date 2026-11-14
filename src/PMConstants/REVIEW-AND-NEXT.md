# PMConstants — open work

- **Strong CP.** The mass phase is not on this route: `ThetaBarSelection.Zm_eq` makes the vacuum see
  only `θ − arg det(M_u M_d)`, so `θ̄ = 0` holds for any invertible mass under its winding-weight and
  vacuum-selection premises (the non-Hermitian crossing of `GenerationParity` and the composite's
  phase are flavour questions). What is missing is the unit-winding witness: two kernels whose
  negative-mode counts differ by one. `WallTransfer` gives the determinant factor for a given
  count and `PMAction.InertiaStability` keeps the count locally constant; neither produces the
  witness. Bring the external unit-transfer certificate into Lean: verify invertibility and the change from 162 to 163 filled modes for the two Wilson kernels, using the inertia-certificate theorem (PMAction item). The anomaly relation is derived (`PMAction.WallTransfer`, `FermionFlip`); the selection argument admits the θ-vacua as least-cost candidates. [Certificate](../../tools/unit_transfer_certificate.py) · [Selection theorem](ThetaBarSelection.lean)
- **Running couplings.** Consume a theorem on the subtracted lattice polarization from PMAction
  (PMAction item "Subtracted lattice polarization": the finite-`q` vertex with its Ward weight
  `FiniteVertex`, the contact term, and a bound that resolves the `q²` coefficient), in place of
  the continuum integrand inside `PMAction.PolarizationRemainder.polarization_window`, whose
  continuum `q`-expansion remainder is already bounded (`500|q|³/μ · 2π² ln(M/μ)`). Inserting
  `w = k + q/2` into `vertex_gap` alone is not the physical vertex (`FiniteVertex.midpoint_gap`). [Polarization remainder](../PMAction/PolarizationRemainder.lean) · [Leading log](../PMAction/LeadingLog.lean)
- **Dressing outlets.** `PMFlavor.DressingEvent.event_law_spatial` works on `Fin 4` labels (no position
  or hop), so the outlet count needs no site move. Open: whether the actual CKM loss realizes that
  event law (zero rate on the time label, equal rate-weighted shares on the three spatial labels) and
  the row-to-outlet identification. Carrier space and the lattice share axis labels only; a carrier
  label change is not a site move (`WeakLocality`, `hL`).
