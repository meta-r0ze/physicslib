# PMConstants — open work

- **Strong CP: the correspondence check.** The witness is in place (OVERVIEW: `UnitTransferWitness`):
  `theta_zero_of_certificates` takes two inertia certificates, and
  `tools/unit_transfer_certificate.py` checks their hypotheses (strict row dominance, `162` and `163`
  negative diagonal entries, `L = 3`) in ball arithmetic; that numerical step is an explicit external
  premise. Open: check that the script's two matrices are the library's backgrounds (the Wilson
  kernel `γ₅(D_W − M)` at `M = r = 1` of `PMAction.DomainWall`, link transports of
  `PMAction.Machine.MatterContinuum`, the constant-flux link phases), for instance by stating the
  kernel in Lean and checking a few matrix entries against the script's builder.
- **Running couplings.** Consume a theorem on the subtracted lattice polarization from PMAction
  (PMAction item "Subtracted lattice polarization": vertex and contact done in `FiniteVertex`,
  `PolarizationContact`; open is a bound that resolves the `q²` coefficient), in place of
  the continuum integrand inside `PMAction.PolarizationRemainder.polarization_window`, whose
  continuum `q`-expansion remainder is already bounded (`500|q|³/μ · 2π² ln(M/μ)`). Inserting
  `w = k + q/2` into `vertex_gap` alone is not the physical vertex (`FiniteVertex.midpoint_gap`). [Polarization remainder](../PMAction/PolarizationRemainder.lean) · [Leading log](../PMAction/LeadingLog.lean)
- **Dressing outlets.** `PMFlavor.DressingEvent.event_law_spatial` works on `Fin 4` labels (no position
  or hop), so the outlet count needs no site move. Open: whether the actual CKM loss realizes that
  event law (zero rate on the time label, equal rate-weighted shares on the three spatial labels) and
  the row-to-outlet identification. Carrier space and the lattice share axis labels only; a carrier
  label change is not a site move (`WeakLocality`, `hL`).
