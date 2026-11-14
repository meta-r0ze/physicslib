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
  3. Chirality within one convention (wall = chirality, `DomainWall`). Found, to formalize: a
     generation-diagonal chirality flip changes the class by the label, which is not an equal-class
     move; the equal-class crossing changes the generation (`PMFlavor.InterWallDiagonal`); the label
     translation keeps each component's wall (no chirality flip) and leaves the convention. So within
     one convention `E₈` supplies no generation-diagonal mass. Then decide the physical source of the
     diagonal mass (a composite of a crossing and a single-wall carrier, or the update containing both
     conventions) and whether spinor-class crossings carry the node suppression.
  4. The charged-current operator on this space: weak is the sign exchange on the reference's
     sector (`PMConstants.CarrierActions.weak`), which keeps every class. Show which single-wall
     carrier events, if any, accompany it, and on which wall; that decides which generation
     changes the charged current makes.
  5. Symmetries: the wall-parity exchange (`WallExchange`) on the generation-changing part. This
     settles whether the inter-wall link is Hermitian (the seesaw fork in `PMFlavor`).
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
