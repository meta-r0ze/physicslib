# PMAction — open work

Done results are in [OVERVIEW](OVERVIEW.md). The protocol layer (how up, down, `e`, `ν` read the
wire) is in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).

## The wire

The wire's light mass is one definition (`WireMass`, carriers placed by single-wall glue arithmetic),
the node amplitude is `k/K = α/2` (`NodeAmplitude`), and the reference's wall is undetuned
(`ReferenceDetuning`). Its inputs were tested by persistence (OVERVIEW, "The wire's inputs"): one `δ_O`
per wall and equal spinor magnitudes are forced; the other wall's vector amplitude and the rate
reading of `k/K` are choices that do not fix the data. Open, wire only:

- **Size of `δ_O`.** No library statement fixes it. Leads: (i) compute the wall-`1` flip as the
  `0 → 2` element of an independently specified, reference-conditioned native update
  (`first_wall_action` extracts it; `NativeFlavourWall.encoded_eigenstate` is the target); (ii)
  `Machine.RootTransferPhase` as an event clock (`δ = −gap(p)/2` for an attempt probability `p`,
  `NativeDetuning.generator_split`); (iii) `WalkReferenceCoupling.preparation_angle_forced` fixes a `β`
  pulse angle `π/4`, so `δ_O = −π/(4N)` for an event of duration `N` in generator time units, if that event performs this preparation.
  One generator unit corresponds to two lazy-transfer ticks; the event duration is open. `δ_O` and
  `ZeroModeCoupling`'s `r − 1` are different matrix elements; tying them needs a derivation.
- **Lazy or coherent `β` event.** Whether a wall's `β` event carries a wall-local scalar phase
  (`WallOffset`: lazy gives squared masses, coherent gives linear) is not decidable in the library;
  state it as a premise. (The data comparison that favoured coherent used the withdrawn placement.)
- **Open premises, stated.** `|y| = 1` (derive whether the bare crossing preserves norm;
  `CyclicSeesaw.crossing_isometry_iff` gives the exact equivalence); admittance versus rate for `k/K`
  (the equal-duration, first-transfer reading gives about `0.0385`); the vector rate `K_f ≪ |y|` as an allowed leakage
  (`LightLeakage.leakage_bound`, the allowed `L` not fixed).
- **Colour and `β`.** Derive how the native update realizes chirality and colour together. On the
  four carrier axes with fixed `ConcreteFermion.gamma`, a colour-permutation-invariant chirality
  flip vanishes (`NativeDetuning.colour_invariant_flip_zero`). A separate spinor index would
  allow colour to act independently; its identification in the substrate remains open.
  Averaging a protocol readout over colour requires its own measurement rule.
- **Physical price of the even complement.** Establish whether invisible-mode squared displacement
  carries a positive toll and the identity completion is admitted by the microscopic gates.
  Under those premises persistence selects identity (`CompletionSelection.most_persistent_in_family`).
- **Update as `e^{−iHt}` on wall modes.** `PMAction.FlavourEvolution` takes the flavour evolution as
  `U e^{−iEt} Uᴴ` with supplied `U`, `E`, and the transfer-cost chain in PMFlavor
  (`ReferenceSelection` → `RelativeFrameCost` → `TransferWorkLaw`) is built on it.
  `WallLatticeSpectrum` states the gap: the finite-tick substrate update is not identified with the
  wall Hamiltonian's exponential, and no physical clock is fixed. Show whether the update at the
  clock acts on the wall modes (`NativeFlavourWall`) as `e^{−iHt}` for some `t` set by `Δ`; until
  then the transfer-cost results are conditional on it. Falsification: an update whose action on
  the light wall modes is not a function of `H` alone. The flavour wire needs one number from this item: the duration of one
  carrier event in hop-time units (`CertainTransferRate`; the `δ_O` item above).

## Carrier update

- Certify the lowest positive carrier level on the full 216-dimensional operator, then certify the spin-up rms radius in Lean. The exact subspace calculation is in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`; the full-space level ordering still uses floating point.
- Find the physical axial current of the carrier. The two-slice update's own local axial rotation is the slice sign: it commutes with every hop and the on-site term and is broken only by the inter-slice coupling, and its link current `sym(S v_j)` is exactly normalized for free carriers (`tools/slice_axial.py`). On the confined carrier it gives `0.22–0.45` (`n = 3…8`) against the on-site `Σ_z` `0.83–0.67`, extrapolating to about `0.5` against `0.65`: with two slices the wall leakage is `O(1)`, so this current neither confirms the on-site operator nor gives a usable `g_A`. Next candidates: the many-slice limit of the wall, or the vector-axial Ward identity at nonzero momentum transfer. The [hadron calculation](../PMHadrons/REVIEW-AND-NEXT.md) needs this current and pion source.

## Dynamics and limits

- Lattice polarization, optional sharpening (OVERVIEW: `PolarizationShellIntegral`). (i) Replace the
  continuum shell by a concrete Brillouin-zone sum. Instantiate the wrap identities in
  `PolarizationContact.finite_routing_cancel` and handle singular zero modes in a shift-compatible way. (ii) A sharper constant than `K = 271853128/3`, so that the bound gives the size
  of the lattice correction at a fixed `a`. The numeric target is `C a² (hi² − lo²)` with `C ≈ 1.38`
  (`tools/lattice_polarization_check.py`). Falsification: a proved constant below `1.38` would
  contradict the numeric check.
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Determine where the directional update fixes the invisible complement. For a shared encoded action,
  this is the exact condition for agreement with the on-site extension (`CompletionSelection.agreement_iff`).
  The five-site directional factor already has a distance-two entry at arbitrarily small ticks
  (`NativeLocalityBoundary.arbitrarily_small_second_hop`); unconditional factor equality fails there.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.

