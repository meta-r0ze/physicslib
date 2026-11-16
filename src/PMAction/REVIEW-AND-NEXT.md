# PMAction — open work

## Generation sector

The six-step plan is done, and the wire's mass form is derived (OVERVIEW: `GenerationSector`,
`CarrierFlip`, `ReferenceDetuning`; `PMAction.ReferenceWallMass`: `M = D_R (δ_O + cyc κ_O)`). How
each species uses the wire is protocol work in
[PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md). The node amplitude is
derived (`PMAction.NodeAmplitude`: `k/K = α/2`). Open, wire only:

- **Size of the other wall's detuning `δ_O`.** `ReferenceDetuning`: the reference's wall is
  stationary exactly when `δ_R = 0` (`stationary_iff`), and the other wall's chiral state exactly when
  `δ_O = 0` (`stationary_first_iff`); so `δ_R = 0` and the light mass is `M = D_R (δ_O + cyc κ_O)`
  (`ReferenceWallMass`). `δ_O = 0` gives `UndetunedWall`'s `(|K k_s|, |K k_s|, |k_c|²)`; calling that
  "two heavy, the reverse of the data" uses its class bookkeeping and `|K k_s| > |k_c|²`, so the
  exclusion of `δ_O = 0` rests on those premises plus the observed ordering, not on stationarity. No
  library statement fixes `|δ_O|`. Note: `δ_O` is the on-site flip on wall `1` (`Γ = +1` to `Γ = −1`
  on the same wall, `first_wall_action`); `ZeroModeCoupling`'s `r − 1` is the inter-wall hop's direct
  light-to-light element. They are different entries; tying them to one parameter needs a derivation
  (and a changed inter-wall Wilson hop also adds a direct light term the seesaw form omits).
  **Rotation on the event's wall** (`ReferenceWallRotation`): off-diagonal `M Mᴴ` entries are
  `dᵢ(δ̄ κ + δ κ̄)d̄ⱼ`; the charged current reads this side (rows of `D₂ Y⁻¹ D₁ᴴ`, the wall
  `(1 − Γ)/2` selects; one step by name). First-order rotation `≈ |dᵢ/dⱼ| · |κ_O/δ_O|`.
  **Numerical facts (outside Lean, 2026-11; items 1–4 and the triage rows on the golden point and the
  wire's own `U` used the superseded bookkeeping, vector carrier at `(1, 0)`; with the corrected one see
  the bookkeeping item below and PMFlavor REVIEW "Redone").** Symmetric bookkeeping, vector flip
  `K_f`, spinor flip `k_f`:
  1. *Ordering:* one heavy, two light once `|δ_O| ≳ k_f`.
  2. *Light pair (corrected).* The wire itself splits the light pair when `|δ_O|` is a few `k_f`: the
     light ratio runs from `≈ k/K`-level at `δ_O ≲ k_f` through `0.03–0.5` at `δ_O = 5 k_f` to near `1`
     at `δ_O ≳ 30 k_f` (sign of the repair matters). An earlier entry said "degenerate for every
     `δ_O`"; it scanned only `δ_O ≥ 0.1 K_f` and is withdrawn. At large `δ_O` the residual split is
     `2|b|` with label-equal mixtures. So in the regime `δ_O ∼ k_f` the wire gives all three masses
     from one ratio `δ_O/k_f`: a one-parameter curve relating the two mass ratios of a sector. That
     curve is a wire prediction; comparing it with species is PMElementaryParticles work.
     `WireLightSplit`: the two larger masses are `K` times the eigenvalues of `[[δ_O, k], [k, 0]]`
     (`√(m₀/m₁) − √(m₁/m₀) = δ_O/k`; at `δ_O = k` the Fibonacci matrix, masses `K k φ`, `K k/φ`), the
     third `≈ k²`; so `(m₂/m₁)√(m₀/m₁) ≈ k/K`, parameter-free in the ratios.
  3. *Heavy–light rotation* `≈ k_f/|δ_O|` (exact two-wall: falls faster above `δ_O ≈ 0.3 |y|`). In the
     regime of item 2 it is `O(0.1–1)`, so `U ≠ 1` there.
  4. *Full two-wall check* (blocks `a, b, c, d` of `WallSeesaw`): the reduction `D₂ Y⁻¹ D₁ᴴ` misses the
     heavy mass by `25%` at `δ_O = 0.3|y|` with `K_f = |y|/2`; then about `20%` of the heavy state lies
     on the gapped components.
  **Open premises, stated (from a review, 2026-11).**
  - `|y| = 1`: `CyclicSeesaw.gram_equal` holds for any common crossing `a`; `|a| = 1` needs the added
    premise that flavour transport across the bare hop is a unitary relabelling.
  - Rates vs admittances (`CertainTransferRate`): admittance is a probability per event, `t` a rate.
    With `P = sin²(tτ)` and equal durations on the first-transfer branch, `t_s/t_v =
    (2/π) arcsin √(α/2) ≈ 0.0385`, not `α/2`; `k/K = α/2` is an admittance ratio and carries over to
    rates only through a stated readout. Both values of `k_f/K_f` are kept as readings; item 2's
    regime exists for both.
  - The vector rate: if light states must have small weight off the zero kernel (`ChiralLightBand`
    gives the projector identity, not a leakage bound), `K_f ≪ |y|`. Stated as a regime with an
    allowed leakage, not derived.
  - The weak refresh (every tick) is a label sign exchange, not a carrier hop: it does not fix `t_v`
    (an earlier entry said it did; withdrawn).
  **Leads.** (i) Compute the wall-`1` flip `δ_O` as the `0 → 2` element of an independently specified,
  reference-conditioned native update (`first_wall_action` is the extraction formula; a generator
  with `δ` already inserted would return the input; `NativeFlavourWall.encoded_eigenstate` is the
  comparison target). (ii) `Machine.RootTransferPhase` (`gap`, `quarterTime`,
  `integer_tick_calibration`) is a conditional event clock: a bridge for the carrier rate if a
  carrier event is identified with that pulse and its tick count is obtained independently (its
  quarter pulse is a `π/4` rotation, not the certain transfer). Read as a rate law: an attempt
  probability `p` per tick gives the generator rate `gap/2 = −log(1 − 2p)` per tick, `≈ 2p` for small
  `p` (rate proportional to admittance, so `k/K` carries over for two small attempt rates), and
  unbounded as `p → 1/2`. So in this construction a certain vector event has no finite rate: one more
  reason `K = 1` is not a rate, and the vector rate needs its own attempt probability. (iii) Whether the reference-fixed
  symmetries still exchange the two light carriers' matrix elements (`LightSplit`,
  `ChannelSymmetry.flip_class`, `closure_one_price`'s premise).

- **Triage of the `δ_O` leads (2026-11, one cheap check each).**
  | Lead | Cheap check | Result | Next |
  |---|---|---|---|
  | Leakage bound (`ChiralLightBand`) | full two-wall, heavy state's weight off the zero kernel | `≈ 1.1 (K_f/|y|)²`, quadratic, stable for `K_f ≤ 0.2` | done: `LightLeakage.leakage_bound` (exact): leakage `L` holds once the largest flip is `≤ √(L/(1−L)) (|y| − |E|)`; the allowed `L` is not fixed by the library |
  | Two-detuning native wall | `NativeFlavourWall`, `NativeSector.diag`, `WallExchange.H` use one `δ` | done: `WallExchange.H2`, `NativeFlavourWall.nativeHamiltonian2`, `native_observed2` | target for the native measurement: reproduce `δ₁ β` on wall `1` at `k = 0` |
  | Native `δ_O` measurement | search for a reference-conditioned native update | none in the library | parked until the two-detuning wall exists |
  | Rate law (`RootTransferPhase`) | a vector attempt probability in the library | none (`RootPulseEvents`: one attempt is not the quarter pulse) | parked |
  | Golden point `δ_O = k` (`ℤ[φ]`) | icosian / `H₄` structure in the library | none; direct species reading fails (ratio `φ²`) | parked; candidate needs `H₄` folding in PMSubstrate and a protocol reading |
  | Economy-minimal `δ_O` | sharp value? | crossover, not a point | dropped as a value source |
  | Rate vs admittance ratio (`α/2` or `0.0385`) | `WireLightSplit` relation against species | both fail directly (recorded, EP) | kept as readings |
  | `δ_O` vs `r − 1` | same parameter? | different matrix elements (`first_wall_action`, `zero_mode_element`) | needs a derivation tying them, or keep apart |
  | Hygiene | unused hypotheses | removed (`node_series`, `one_wall_flip`) | done |
  | Native `δ_O` as a `β`-event rate | `NativeDetuning` | `δ = −gap(p)/2`; `β` swaps axes `0 ↔ 2`, moving half the vector carriers across the node once | leg count open: golden (`δ_O = k_f`) or silver (`≈ 2k_f`) candidate |
  | Wire's own `U` as the persistence rotation | `U_uᴴ W U_d` with the wire's reference-wall `U` common to both protocols | `|V_ub| = 0.026–0.12` at every `δ_O` (PMFlavor REVIEW item 6) | excluded: `U` is protocol-level |

- **Bookkeeping of the other wall's carriers (found 2026-11, affects `UndetunedWall`,
  `WireLightSplit`, `UpDownWire`).** `GenerationCurrent` (wall `true`: `g → g + 1` uses class `g − 1`) and
  `GenerationWeak.weak_edge_true/false` (the vector carrier joins generations `1` and `2`) put the
  vector-class carrier on the light pair, entry `(2, 1)` of `cyc κ_O`; `UndetunedWall` put it at `(1, 0)`
  (class `h` at `(h + 1, h)`). With the matching assignment (shift `(k, K, k)`, rows `(K, k, k)`):
  - `UndetunedWall`'s undetuned masses are unchanged as a set (`k², kK, kK`);
  - `LightPairTexture`: the light block is `k [[δ, 0], [K, δ]]`, giving `tan θ₁₂ = √(m₁/m₂)` exactly at
    that order (Gatto–Sartori–Tonin), and the heavy–light rotations become tiny (`≈ 10⁻⁴`);
  - `WireLightSplit`'s Fibonacci block and the numerical studies built on the old assignment
    (light-pair `45°`, `U` exclusions in PMFlavor item 6, the protocol-`U` test in
    PMElementaryParticles) must be redone with the matching one before they are relied on.
  Next: restate `UndetunedWall`'s bookkeeping with the class at `(h + 1, h)` derived from
  `GenerationCurrent`, then redo `WireLightSplit` and the dependent numerics.
- **Lazy or coherent `β` event: the data favour coherent (2026-11).** With the corrected bookkeeping,
  the squared (lazy, wall-offset) reading breaks the GST relation (`tan θ₁₂ = 0.43` for down against
  `√(m_d/m_s) = 0.224`) and misses the second ratios by `100×` or more; the linear (coherent) reading
  keeps GST and lands down and leptons within `10%`. So a wall's `β` event acts as a coherent
  rotation (no wall-local scalar phase); `NativeDetuning`'s lazy identification is disfavoured.
- **Lazy or coherent `β` event (decides the mass formula).** `WallOffset`: the lazy reading of a
  wall's `β` event (`NativeDetuning`, `RootTransferPhase`) leaves an energy `|δ_O|` on the other wall
  only; the light masses become `≈ s²/|δ_O|` (squares of the wire's singular values), while a
  coherent traceless rotation gives `s`. `U` is the same in both. Decide which the substrate's event
  is: compress the full native generator onto the wire with the library's wall order, allowing one
  global scalar, and see whether `c P_O` survives (no new premise). Checked (2026-11): not decidable
  in the library. The native wall model (`StateIdentification.NativeSector.diag`,
  `NativeFlavourWall`) takes `δ β` as an input, the coherent form; `RootTransferPhase.quarter_pulse`
  keeps the lazy transfer's scalar phase; the reference preparation pulse
  (`Machine.WalkReferenceCoupling.preparation`) is a coherent `β` rotation. Whether a wall's `β`
  event carries a wall-local scalar phase is a premise to state, with the squared versus linear
  mass formula as its test. Recorded (direct readings, rough):
  the squared reading's version of `WireLightSplit`'s relation, `√(m₂/m₁)(m₀/m₁)^{1/4}`, is `0.14`
  (leptons), `0.58` (down), `0.14` (up), against `k/K = 0.0037` or `0.0385`: fails directly, like the
  linear one.
- **Leads from a review (2026-11), not yet run.** (B) `Machine.WalkReferenceCoupling.preparation_angle_forced`
  forces a `β` pulse angle `π/4` for the pure-forward preparation of a wall-`1` seed; with
  `RootTransferPhase.integer_tick_calibration` that gives `δ_O = −π/(4N)` per generator unit for an
  event lasting `N` (lazy-transfer ticks count twice), `N` not fixed. (A) Native intertwining
  (`CarrierWeyl.intertwining`, `OddCarrierPhase.phase_sector`) makes any mechanism using the same
  word, preparation, time and readout give equal magnitudes for the two spinor classes; a wall
  asymmetry must come from a different preparation, intermediate projector or timing on the two
  walls (the stationary background is one). Compute a reference-conditioned leg response
  (`Machine.ReferenceSampling.ref_flag`) on each wall before giving it a price.
  (A/B) Repair-cost odds (`RootTransferAccounting.gibbsRate_formula`, `FactorRepair.repair_least`)
  would relate attempt odds, not rates, if `β` and a carrier leg share the ensemble and cost unit.
  Run (A): `ReferenceLegSymmetry.flag_conj`: a reference-fixing unitary leaves the leg flag
  unchanged, and a colour reflection fixes the reference and exchanges `s`, `c`; so
  reference-readout leg prices give no `s/c` magnitude asymmetry. Excluded.

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
  continuum shell by the Brillouin-zone sum, where the routing difference of `bubble_sub_contact`
  cancels by a shift. (ii) A sharper constant than `K = 271853128/3`, so that the bound gives the size
  of the lattice correction at a fixed `a`. The numeric target is `C a² (hi² − lo²)` with `C ≈ 1.38`
  (`tools/lattice_polarization_check.py`). Falsification: a proved constant below `1.38` would
  contradict the numeric check.
- Construct the map from background `Config` to the `RecordSupply` stream used by `ReferenceSelection`. Physical allocation of the banks is a [machine-layer dependency](Machine/REVIEW-AND-NEXT.md).
- Establish shared group and trace normalization across spacings. Multi-pass root words are tracked in the machine review.
- Identify the directional-exponential completion with the on-site completion, or specify the conditions for their agreement.
- Establish mode and domain control for the real-space PDE limit, the integrated Hessian, the full real-space fermion field and interacting-field estimates.

## The up protocol's heavy on-site entry (2026-11, open)

Data (PMElementaryParticles REVIEW): the down and electron protocols fit one `δ` on all three
labels; the up protocol fits only if its heavy (vector-class) label has on-site entry `K` instead of
`Kδ` (`m_c/m_t` `0.98×`; with `δ`, `23×`). `PMElementaryParticles.BetaReference.onto_reference_iff`:
that label is the only (protocol, label) slot whose `β` image is the reference carrier.
- Task: derive the on-site entry of a label whose `β` image is the reference carrier, from the
  wall structure (`LightSplit.composite_expansion2`, `NativeDetuning`, `ReferenceWallMass`).
  Candidate premise: the transition is carried by the reference-class carrier, entry `K`.
- Colour test: the fixed `β` (`CarrierWeyl.realMatrix 0`, pairing axes `0 ↔ 2`) reaches the reference
  from one colour only (`one_colour_onto_reference`). Colour-covariant pairing gives `K` (`0.98×`);
  colour-averaged gives `K/3 + 2δ/3` (`2.7×`). Derive which.
- Structure (`BetaReference.beta_fixes_none`): on the vector-class label `β` fixes no carrier, so an
  on-site entry there is a `β` round trip (amplitude² / gap of the image). The up protocol's paired
  carrier has the reference zero mode as image: zero gap, resonant, entry of order the `β` amplitude.
  Candidate mechanism for the one large entry. **Problem found:** off the paired axis `β` maps a
  colour-`1` carrier to the same protocol's colour-`3` carrier, also degenerate, so colours `1`, `3`
  of both quark protocols mix at first order. A fixed `β` on the carrier axis index splits colour
  within a protocol, against `ReferenceStabilizer.colour_unbroken`. `NativeDetuning`'s identification
  (on-site `β` = `CarrierWeyl.lookup c 0` on the axis index) needs a colour treatment first: `β` on a
  separate index commuting with colour, or colour-averaged. This blocks the per-slot derivation and
  may be an error in `NativeDetuning`'s reading for coloured protocols.
- **Second problem found:** the wire's `β` acts in the coordinate-odd sector
  (`CarrierVacuumSector.range_iff_odd`), whose axis-`i` mode is `|+2eᵢ⟩ − |−2eᵢ⟩`. The doublet sign is
  fixed there, and `β` maps axis mode `2` to axis mode `0` with no sign. So `BetaReference`'s
  up-versus-down distinction holds for single carriers but does not reach the wire as written.
  Needed first: how a protocol's doublet sign sits on the wire, given that only odd modes are
  admitted. Until that is settled, the up heavy-entry candidate has no wire-level source.
- **Where the sign lives (`PMElementaryParticles.DoubletSign`).** Weak partners are antipodes, and
  every native word commutes with the antipode; the wire keeps only antipode-odd states, and the
  even complement is inert by convention (`CarrierVacuumEvolution.even_inert`, an open obligation).
  So the up/down difference between partners is the cross term `2 Re ⟨odd|H|even⟩`, zero in the
  current model. The only antipode-odd input is the reference carrier (`+2e₀`, not its antipode).
  Next test: give the even complement the action induced by the reference's maintenance and compute
  the cross term per (protocol, label). Zero means the difference must come from how a protocol
  reads the wire, not from the wire.
- **Cross-term test, analytic (2026-11).** Simplest antipode-odd term: a shift `ε |ref⟩⟨ref|` on the
  reference carrier `+2e₀ = (odd₀ + even₀)/√2`. Its cross term `⟨odd|H|even⟩` is `ε/2` on axis `0` only:
  first order for the lepton-axis partners (`ν` vs `e`). The colour axes get it only through a
  transport to axis `0`: with the fixed `β` (`0 ↔ 2`, commuting with the antipode) at second order on
  colour `2` only, colours `1`, `3` none. So with a fixed `β` the reference splits up from down on one
  colour only, which unbroken colour forbids. A colour-symmetric transport (the average of the three
  colour conjugates of `β`, each pairing one colour axis with `0`) gives all colours the same second-order
  cross term, `1/3` of the fixed-`β` amplitude per colour. This is the "colour-averaged" reading
  (`BetaReference`), which in the resonant-`K` model gives `m_c/m_t` at `2.7×`.
- **Why the wire is odd (`FullCarrierIdentification`).** Carrier permutations fix the uniform mode,
  which is even, and anticommuting generators cannot share a fixed mode
  (`common_fixed_obstruction`, `no_full_permutation_clifford`). So the Dirac (Clifford) structure
  lives only on the odd sector: the wire's fermion field is odd by structure, and the doublet sign,
  carried by the odd/even combination of a single carrier, is not a property of a wire mode.
  Reading: the up/down (and `ν`/`e`) difference belongs to the protocol layer, how a protocol's
  carrier `(odd ± even)/√2` reads the shared wire, as PMFlavor already frames it (protocols over the
  wire). Open: a protocol-layer readout whose result depends on the sign; it needs an even-sector
  partner for the protocol's even half (the reference is the only antipode-odd candidate).
- Checked and excluded: an on-site term on the reference wall's heavy row (`δ_F` at label `v`, the
  other natural placement) moves `m_c/m_t` only to `13×` at `δ_F = K` and disturbs the light pair.
- Falsification: a derivation giving `δ` (or the averaged entry) for that slot retires the
  candidate; the up protocol's miss then stays open.
