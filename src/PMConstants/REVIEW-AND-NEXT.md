# PMConstants — open work

- **Strong CP.** Bring the external unit-transfer certificate into Lean: verify invertibility and the change from 162 to 163 filled modes for the two Wilson kernels. The anomaly relation is derived (`PMAction.WallTransfer`, `FermionFlip`); the selection argument admits the θ-vacua as least-cost candidates. [Certificate](../../tools/unit_transfer_certificate.py) · [Selection theorem](ThetaBarSelection.lean)
- **Running couplings.** Bound the finite-spacing errors in the polarization integral over the window: replace the continuum propagator and vertex by the substrate's (`symbol_gap`, `vertex_gap`) inside `PMAction.PolarizationRemainder.polarization_window`, whose continuum `q`-expansion remainder is already bounded (`500|q|³/μ · 2π² ln(M/μ)`). [Polarization remainder](../PMAction/PolarizationRemainder.lean) · [Leading log](../PMAction/LeadingLog.lean)
- **Audit: two readings of the two `D₄` summands.** `WeakLocality`'s docstring reads `E₈ = D₄ ⊕ D₄`
  as "spacetime and internal" (one summand each); `PMAction.DomainWall` and the 38 modules built on
  it read the two summands as the two walls, copies of one lattice with opposite chirality
  (`GenerationWalls`, `WallExchange`, the flavour sector). These cannot both hold. Check whether
  `WeakLocality`'s argument needs the spacetime/internal reading. Checked: it does not; the proofs
  take "weak's displacements have no spatial component" as a hypothesis (`hL`), and the docstring
  is reworded. **Found a real conflict instead:** `CarrierActions.weak` flips all eight vector
  carriers of the reference's sector, six on colour axes. Two premises disagree about those six.
  `PMFlavor.DressingInheritance` (and `PMFlavor.TickPlacement`) take carrier vectors to be lattice
  hop directions; then flipping a colour-axis carrier is a spatial displacement `−2v`. `WeakLocality`
  takes weak to move no site (`hL`), which the frame ledgers `43`/`129` (`rows_from_locality`) rest
  on. Both hold only if carrier labels are not hop displacements, which is the negation of the
  first premise. Settle which is right, or restrict one: e.g. the shared-coordinates premise only
  for the reference carrier (time axis), which is all `DressingInheritance.refresh_along_own_axis`
  uses; then check whether `DressingEvent`'s spatial-outlet count (`3`) and `TickPlacement`'s
  class-in-time counts still follow. Results that depend on this: the `515/516` dressing, the frame
  ledgers, `TickPlacement`.

