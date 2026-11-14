# PMAction — open work

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
- The phase of a node-crossing hop. `WallHopPhase` shows in-wall spatial hops carry a quarter turn
  that cancels in every reduced coupling, so the CKM flux (`PMFlavor/REVIEW-AND-NEXT.md`, about
  `49°`) must come from elsewhere. The node crossings are spinor-class displacements with a
  time-axis component `±1` (`PMFlavor.ExchangeAxis.spinor_touch`), which is not a spatial `αⱼ`
  hop. Compute the amplitude of such a displacement on one chirality, in the discrete-time update
  (the time component is a tick, not a hopping term), and its phase relative to the in-wall legs.
  Also state the lead model (equal leads per generation) here as a premise, since
  `PMFlavor.TransferGenerator` uses it.
- A direct zero-mode mass term. `ZeroModeCoupling`: the direct coupling of the two zero modes is
  the off-Wilson part of the inter-sector hop, `(r − 1)·βx`; at the library's Wilson point `r = 1`
  it vanishes and the equal-class crossing reaches the light modes only through the gapped
  components (the `WallSeesaw` route, size `δ²/|Y|`). The flavour sector (`PMFlavor.MassInsertion`)
  needs generation-diagonal masses set by a label-class insertion, so the candidate is a
  class-dependent `r_m − 1`. Open: (1) why a label-class insertion would shift the Wilson
  parameter. Closed route: the plane-wave phase. A class-`a` inter-wall hop joins `x` to `x + d`
  (`d` a minimal vector of class `a`) and carries `Σ_d e^{ip·d}`; at `p = 0` this is the class size
  `8` for every class, so the class offset reaches only the doublers, not the zero mode's `r − 1`.
  What is left is the hop's spinor structure: every spinor-class displacement has a time-axis
  component `±1` (`PMFlavor.ExchangeAxis.spinor_touch`), six of eight vector-class ones have none
  (`vector_free`), and a time-axis step is a tick of the update, not an `αⱼ` hop. So build the
  two-slice wall as a discrete-time walk (the `DomainWall` note: not built yet) with class-`a`
  inter-wall hops whose time component advances the tick, and compute the zero-mode element
  per class. Plan: (i) numerical model in `tools/` at `p = 0` (24 components: spin × wall ×
  generation), built from the existing factors (`LocalUnitary`, `SplitUpdate`, `VacuumSplit`
  ordering) plus class-labelled crossings, with the time component in each candidate placement
  (left or right factor, projector or phase); forward (`d₀ = +1`) and backward displacements sit
  in `U` and `U†`, so they need not cancel as they do in the Hamiltonian. (ii) Keep placements that
  are unitary, local (`Supported`), vacuum-preserving (`VacuumSplit`) and reduce to the generator
  identity as `τ → 0`. (iii) Test them as below; if none passes, the direct-mass candidate is closed.
  (iv) Lean only for a surviving placement. Blocker found when starting (i): the library has no
  map between carrier classes and walk steps (the 27-site stencil comes from the axis permutations of
  `SplitUpdate`, not from `D₄`), and at `p = 0` the update is exactly the wall coin
  (`VacuumSplit.origin_update`), so a class-labelled model would build in its answer. Candidate
  premise, to be derived or tested, not chosen: one wall's `D₄` (even-sum model) is the walk, with
  axis 0 (the reference axis) as time. Its consequences (checked numerically): the `D₄` roots at
  `t = +1` are exactly the six axis moves, and the corner `(1,1,1)` at `t = 1` is a `D₄` vector (the
  three-axis composite), consistent with `DiscreteCausal`'s 27-site reach; vector-class carriers are
  six equal-time axis displacements and two pure ticks; both spinor classes sit at half ticks
  `t = ±½` with corner spatial parts. So the node-crossing (spinor) insertions would be half-tick
  events, between walk ticks, where the reference refresh acts. Next: state the identification as a
  Lean premise and prove these counts (`decide` on the even-sum model); check it against
  `DiscreteCausal` and the refresh timing (`PMAction.Machine`); then redo (i) with spinor
  insertions as half-tick factors (`U^{1/2}` placement is then fixed by the identification, not
  chosen). Already found: a Wilson time projector `(1 − β)/2`
  multiplying the crossing on the left still annihilates the zero mode; on the right it lands in
  wall 1's gapped `Γ = −1` component. Test: the vector class must give the larger direct coupling (the heavy, weakly mixed
  generation, `PMFlavor.MassInsertion`), and the two spinor classes must differ only through which
  one sits on the weak wall (`PMFlavor.ExchangeChirality`); (2) whether `δ²/|Y|` from the equal-class
  crossing is small against `r_m − 1`, else it puts generation off-diagonal entries back into the
  mass matrix; (3) the discrete-time version (`DomainWall` is the continuous-time Hamiltonian).

