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
  **Numerical facts (outside Lean, 2026-11).** Symmetric bookkeeping, vector flip `K_f`, spinor
  flip `k_f`:
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
