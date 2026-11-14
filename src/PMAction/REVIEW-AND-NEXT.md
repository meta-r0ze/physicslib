# PMAction — open work

## Generation sector

- **Generation sector of the update (foundation for `PMFlavor`; work through in order).** The flavour
  sector's open forks all reduce to what the update does to generations. Steps:
  1. Moves on the glue labels. Done (`GenerationSector`): `E₈` translations conserve the label, keep
     a generation state only for `a ∈ {0, label}`, and translation by the label swaps the walls'
     classes (keeps the label, reverses the orientation: it maps between the two conventions, not
     within one); generation changes need a
     single-wall `D₄*` carrier, and from `(b, c)` the change to label `b` is a class-`c` carrier on
     wall 1, the change to `c` a class-`b` carrier on wall 2.
  2. Relate the two encodings. Done (`PMConstants.GenerationOrientation`, for every identification of
     `Fin 3` with the classes): `GenerationWalls`' generation `g` is the pair
     `(e (g + 1), e (g − 1))` with label `e g`; `side` picks one orientation per label; swapping a
     whole generation's walls keeps the label and leaves the convention. So `GenerationWalls`' index
     is the label with the orientation frozen, and its "crossing changes generation" is, in label
     terms, an orientation reversal. Its single-component crossing changes the two walls' classes by
     different amounts, which is not a move `GenerationSector` allows; whether it is physical is
     step 3.
  3. Chirality and the diagonal mass. Done (`PMConstants.GenerationMass`): within one convention no
     single allowed move is a generation-diagonal mass; an equal-class crossing plus a single-wall
     carrier of the generation's own label class is, in either order (second order, through another
     generation). Reading: the crossing is class-independent (`DomainWall`'s hop), the carrier
     follows `PMFlavor.ExchangeAxis` (vector mostly in-cycle, spinor through the node), so one heavy
     generation (label `v`, the weakly mixed one) and two light. Open: the node factor's size, and
     the light pair's split (degenerate at this order; the weak wall distinguishes the two spinor
     classes). Not pursued: an update containing both conventions (`no_further_modes` leaves no room).
  4. Generation changes. Done (`PMConstants.GenerationCurrent`): within one convention no single-wall
     shift changes the generation; a single-wall carrier (the other wall's class) plus an `E₈` glue
     move (the intermediate's label) does, `g → g + 1` on wall `true` and `g → g − 1` on wall `false`,
     a directed 3-cycle per wall. The vector-class carrier edge joins the two non-`v` generations;
     both edges at the label-`v` generation use spinor carriers (the coarse CKM pattern with
     `PMFlavor.ExchangeAxis`). `PMConstants.GenerationWeak`: the weak carrier is vector class, so it
     makes exactly the change between the two light generations (`1 ↔ 2`, the Cabibbo transition);
     every change at the heavy generation `0` needs a spinor carrier, which weak's events do not
     supply, so it comes through the reference node: the structural reason `|V_ub|`, `|V_cb|` are
     suppressed. Which wall is "the reference's" is a convention; only the relative orientation of
     convention and charged-current wall is physical (`relative_orientation`). Open: the
     amplitude with which the node supplies a spinor carrier, in the same units as the vector edge.
  5. Wall-parity symmetry. Done (`PMConstants.GenerationParity`): within one convention the
     equal-class crossing sits only at `(h + 1, h)` (one direction around the cycle), never at a
     transposed position, so the link is Hermitian only if zero. The exchange symmetry is broken by
     the vacuum's convention, as chirality is. `PMFlavor`'s seesaw fork is the directional case; with
     `DomainWall`'s single hop the three seesaw masses are equal, so the hierarchy is the composite
     of `GenerationMass`.
  6. Then hand to `PMFlavor`: the mass matrix and the mixing as whatever steps 1 to 5 give.

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.
- Mass terms of the two-wall Hamiltonian. (1) A direct light-mode term: `ZeroModeCoupling` locates
  it as the off-Wilson part of the inter-sector hop, `(r − 1)·βx`; the wall at `r = 1` has none, and
  no source of `r ≠ 1` (or another direct term) is identified. (2) The inter-wall link `Y_gap` the
  E₈ gluing allows is directional (a weighted cyclic shift, `PMFlavor.InterWallDiagonal`); it is
  Hermitian only under the wall-parity exchange symmetry (`WallExchange`). Decide whether the
  physical update has that symmetry for the generation-changing crossing: if yes, `Y_gap` cannot
  carry a charged hierarchy through `WallSeesaw`; if no, `WallSeesaw` gives one Dirac pair per class
  with mass `δ²/|y_c|`, and the class amplitudes decide the pattern. (3) Bound the seesaw
  contribution against any direct term (else generation off-diagonal mass entries return).
- Lead coupling (if pursued): a microscopic derivation of how the generations couple to the leads of
  the charged-current transfer. The equal-width assumption itself is a flavour-model premise owned
  by `PMFlavor.TransferGenerator`.
