# PMConstants — open work

- **Strong CP: the correspondence check.** The witness is in place (OVERVIEW: `UnitTransferWitness`):
  `theta_zero_of_certificates` takes two inertia certificates, and
  `tools/unit_transfer_certificate.py` checks their hypotheses (strict row dominance, `162` and `163`
  negative diagonal entries, `L = 3`) in ball arithmetic; that numerical step is an explicit external
  premise. The spin structure is checked (`PMAction.TorusWilson`: the script's gammas are the
  library's `i β αⱼ`, `β`, with `γ₅ = Γ`, and `wilsonH` is Hermitian for any links). Open: that the
  script's site indexing and link-phase function (constant flux `n₁₂`, `n₃₄`) are `wilsonH` with those
  link values. The link phases are checked (`PMAction.TorusFlux`: constant flux `1/9`, `−1/9` per
  plaquette, charge `−1`). What remains is bookkeeping: that the script assembles `wilsonH` from these
  links in its site order (a code-review statement, or a Lean `build` plus an entry check at a few
  sites).
- **Dressing outlets.** `PMFlavor.DressingEvent.event_law_spatial` works on `Fin 4` labels (no position
  or hop), so the outlet count needs no site move. Open: whether the actual CKM loss realizes that
  event law (zero rate on the time label, equal rate-weighted shares on the three spatial labels) and
  the row-to-outlet identification. Carrier space and the lattice share axis labels only; a carrier
  label change is not a site move (`WeakLocality`, `hL`).
