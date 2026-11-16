# PMElementaryParticles — open work

### A3. Three-body phase-space factorization
The three-body measure is used but not factored. Target: factor it into
(pair invariant mass) × (pair angular measure) × (spectator energy), and derive the
`MassiveDaughterSpectrum` density `pair_density` as a *consequence* rather than an
input. This is the concrete mathematical content of former review item 2.
Uses the two-body phase-space result.

### A4. Massive neutrino pair (extend the daughter spectrum) — tensor done
Done (`MassivePair`): the rest-frame tensor of a pair with masses `m₁`, `m₂` from the same angular
symmetries (`massive_rest_tensor`), its covariant form `Q²⟨k₁k₂⟩ = Φ(P²/3) g Q² + Φ(E₁E₂ − P²/3) q q`
(`massive_rest_covariant`), the massless limit (`massless_limit`), two-body kinematics and shells.
Open: the massive two-body volume (`2P/Q` times the massless one) as a measure statement, and the
daughter-energy integral of `MassiveDaughterSpectrum`/`MassiveWidth` with this tensor.
`MassiveDaughterSpectrum`/`MassiveWidth` treat a massless neutrino pair. Target:
extend `pair_density`/`closed_width` to a massive neutrino pair (at least equal
masses or one massive leg), with positivity and endpoint limits, reusing the
transported pair tensor with `q² ≠ 0`. Closed form or a controlled integral.

### A5. Rotation invariance of the continuum angular average — partly done
Done (`ContinuumPair.average_rotate_polar`, `average_reflect_polar`): invariance under rotations about
the polar axis (any `f` periodic in `φ`) and under `z ↦ −z` (any `f`), no integrability needed. Open:
rotations that move the polar axis (they mix `z` and `φ`; needs the sphere change of variables, or the
identification of `average` with Mathlib's sphere measure and its isometry invariance).
`ContinuumPair` proves moments and linearity on *continuous* test functions but not
full rotation invariance for every integrable test function. Target: prove the
uniform-sphere average is invariant under rotations on `L¹` (change of variables /
Haar invariance of the sphere), so the pair tensor's covariance is a consequence of
the measure, not only of degree-≤2 moments.

## Elementary interactions and protocols

- **Species masses over the wire.** The wire gives one light-mass form,
  `M = D_R (δ_O + cyc κ_O)`, and treats species alike (OVERVIEW, "Species masses over the wire").
  Derive from E8 which protocols exist and how each uses the wire: what it occupies, channel count
  (colour carriers three-fold, lepton-axis one-fold, `PMConstants.CarrierRepresentation`), series
  versus parallel routes (`PMSubstrate.ProtocolToll`: parallel admittances add), node handoffs per
  round trip, the leptons' on-axis geometry, and whether a protocol has a mass matrix of its own at
  all. Derive the routing histories and rates, their costs, and the tiers each protocol occupies
  (`TierLedger.tiersFor`: up `{0, 2, 3}`, down and lepton `{0, 1, 2}`; `QuarkMasses`,
  `LeptonMasses`); the ledgers still need a cost or selection rule for assigning invariants to tiers.
  Do not fit species parameters to measured masses; derive, then test. A wire result to test against:
  `PMAction.WireLightSplit` (regime `δ_O` a few spinor flips): a protocol whose masses are the wire's
  singular values directly satisfies `(m₂/m₁)√(m₀/m₁) ≈ k/K` (`α/2` as an admittance ratio, `0.0385`
  as a rate ratio). A protocol that does not satisfy it uses the wire differently; that is data
  about the protocol, not a fit. Recorded (2026-11, PDG masses, quarks `MS̄` at mixed scales, so
  rough): charged leptons `0.0012`, down-type `0.0075`, up-type `0.00015`; none equals either value,
  so no charged sector reads the wire's singular values directly in that regime. Upstream: PMAction, "Size of
  the other wall's detuning".
  **Up/down over one wire (`UpDownWire`, 2026-11).** The doublet reflection exchanges up ↔ down and
  `s ↔ c` and fixes the reference axis, so with a shared `δ_O`, `K` the down wire is the up wire with
  the light amplitudes exchanged. `product_equal`: same mass product. Numerically the spectra are equal
  for `|k_s| = |k_c|` (any repair sign) and differ for `|k_s| ≠ |k_c|`. So: (i) an up/down split needs a
  light-class magnitude asymmetry, which Closure's node price does not supply; the same asymmetry
  would give PMFlavor's `×10` between the node changes (item 2) and the light-pair split: one target,
  three readouts. (ii) Recorded test: `m_u m_c m_t/(m_d m_s m_b) ≈ 260` (rough), not `1`; so up and down
  do not share `δ_O` and `K` with masses read as singular values. Next: derive where a light-class
  magnitude asymmetry can come from (the leg, not the node: the weak current's chirality,
  `PMFlavor.ExchangeChirality`; the repair acts on one sector) and whether `δ_O` is protocol-set.
  **Round of quick tests on the two open numbers (2026-11).**
  - *Node energy*: not free. `PMFlavor.KronSeries`: in a conserving (Laplacian) link the node's
    diagonal is the sum of its leg conductances, so `e − E = −(g₁ + g₂)`. Only `δ_O` is open.
  - *`δ_O` as a shunt at the other wall's node* (Kron with an extra diagonal term): reference-wall over
    other-wall change `= (α/2)/jump = 1.011`, not `10.7`. Excluded.
  - *Protocol occupancy counts* (which carriers a protocol's state can use per class): symmetric in
    `s ↔ c` by the colour-axis reflection (`DoubletReflection`, `ExchangeAxis`); cannot give a
    magnitude asymmetry. The asymmetry has to come from the wall, not the protocol's axis.
  - *Repair sign*: sign only; `PMAction.WireLightSplit.sign_blind`, `UpDownWire`: no magnitude effect.
  - *Golden/silver `δ_O`* (`PMAction.NativeDetuning`): weak hierarchy (`φ²`, `5.8`) in direct readings,
    and a large `U` there; only usable inside a protocol that adds hierarchy and keeps `U` small.
  - *Protocol-set `δ_O` by `β` crossing fraction* (leptons `1`, colour-averaged quarks `1/3`,
    `NativeDetuning.beta_crossings`): fails the mass-product readings directly; kept as a candidate.
  - *Wall-dependent Wilson parameter*: a carrier flips by `−r t/2` (`PMAction.CarrierFlip`); if the
    other wall's in-wall Wilson `r_O` differs from the reference wall's `1`, then `|κ_O/κ_R| = r_O`: a
    magnitude asymmetry between the walls, the one kind still allowed. Open: what fixes `r_O`, and
    whether it is tied to `δ_O` (`ZeroModeCoupling`: different matrix elements; a single Wilson
    action ties on-site mass and in-wall `r` at `k = 0` only through the Wilson point condition).
    Candidate chain (one premise): the other wall is detuned through its Wilson `r_O` with the on-site
    `M = 1` kept, so `δ_O = 1 − r_O` and `|κ_O/κ_R| = r_O`. Then PMFlavor's node ratio
    `|V_cb|/|V_ub| = 10.7 ± 0.6` (FC, `U ≈ 1`) reads `r_O ≈ 0.093`, `δ_O ≈ 0.91` (hop units): one number
    from the CKM, to be tested against the light-pair split, the up/down split and the leakage bound
    (`δ_O` near the hop scale is where `PMAction.LightLeakage` starts to bite).
    **Excluded** (`PMAction.WilsonPointForced`): the split update's neighbour coefficient
    `(r/2)β + (i/2)αⱼ` squares to `(r² − 1)/4`, so exact local unitarity forces `|r| = 1` on every wall
    it updates. A wall-dependent `r_O` needs the other wall to be updated by a different construction.
  **Reframed (2026-11).** The wall magnitude asymmetry was sought for PMFlavor's `×10.7`. With
  `U ≠ 1` kept, Closure's equal node changes fit the four CKM magnitudes with a 2–3 persistence
  rotation `≈ 0.03` and a cycle phase (PMFlavor REVIEW item 2). So the asymmetry is not required by
  the CKM; the up/down and light-pair splits still need a source, and the protocol-level `U` is now
  the common target for all three.
  **Protocol-level `U`, first test (2026-11, numerical).** The CKM fit with Closure's equal node
  changes wants the 2–3 persistence rotation mostly in the up protocol (`θ_u ≈ −0.034`, `θ_d ≈ 0.004`,
  `χ² = 1.7`; up and down equal and opposite: `χ² = 12`). The wire's reference-wall rotation
  (`PMAction.ReferenceWallRotation`, `≈ |dᵢ/dⱼ| · K/δ_O`) with masses read as the wire's singular values
  predicts the opposite: `θ_u/θ_d ≈ (m_c/m_t)/(m_s/m_b) ≈ 0.33` (linear) or `0.57` (squared reading) at
  equal `δ_O`, smaller still with the `δ_O` ratio the mass products suggest; constrained that way the
  fit gives `χ² ≥ 35`. Recorded: a protocol whose `U` is the wire's own rotation with its masses as
  singular values is disfavoured. The up protocol must use the wire differently from down; the tier
  sets already differ (`TierLedger`: up `{0, 2, 3}`, down `{0, 1, 2}`), which is a lead, not a
  derivation.
  **Lead: a right-handed hypercharge phase on the other wall's carriers (candidate, not derived).**
  What tells up from down is only the right-sector hypercharge (`DoubletReflection`:
  `Y_R = 4/3` up, `−2/3` down; left-handed both `1/3`). The other wall is the right-handed one, and an
  abelian phase rides on every event (`PMAction.Machine.FactorRepair`: "an event may carry any
  phase"). If each other-wall carrier event carries `e^{i Y_R θ₀}`, then:
  - `U` changes per protocol: the reference-wall Gram entries are `dᵢ(δ̄ κ + δ κ̄)d̄ⱼ`
    (`PMAction.ReferenceWallRotation.left_gram_entry`), so a rotation scales with
    `|cos(Y_R θ₀)|`; at `θ₀ = 3π/4` the down rotation vanishes and the up one is maximal, the
    pattern the CKM fit wants (`θ_d ≈ 0.004`, `θ_u ≈ −0.034`);
  - the masses change per protocol through the same entries and through `det = d₀d₁d₂(δ³ + Π κ)`;
  - the cycle product `Π κ` carries `e^{3 i Y_R θ₀}`: a non-flat phase, different for up and down,
    the CP phase's candidate source (PMFlavor item 5).
  **Checked the same day; the `U` and mass parts are withdrawn.** Per-carrier phases are removed by
  rephasing the label states (rows and columns by the same phases keep `δ · 1`); only the cycle
  phase `Φ = arg(κ₀κ₁κ₂) − 3 arg δ` is physical, here `Φ = 3 Y_R θ₀`. The `cos(Y_R θ₀)` scaling above
  was not rephasing-invariant. Numerically, `Φ` moves `|U|` by under `1%` and the two larger masses
  not at all (`δ_O/k = 1, 3, 10`); it moves only the lightest mass (through
  `det = d₀d₁d₂(δ³ + Πκ)`, up to `40%` at `δ_O/k = 10`). So it cannot give the up-dominant 2–3 rotation.
  It stays a candidate for the CP phase only, and needs a non-flat holonomy around the label cycle,
  which persistence disfavours without a source (`PMAction.FlatPersistence`); the only charged
  stationary object is the reference background (lepton doublet, `PMConstants.ReferenceCharge`).
- **Tier ladder.** `TierLedger` (`Δ⁰…Δ³`, up `{0, 2, 3}`, down and lepton `{0, 1, 2}`) is this folder's:
  where each protocol's three label states land. Derive that placement; PMFlavor's label changes act
  on the label states and do not use the ladder.
- Connect the charged-current operator to the contact vertex in `AmplitudeTrace`. Identify the external carrier states, physical mode weights, and readout normalization.
- Supply the physical tick calibration for `DecayLaw`. Identify the low-energy radiative contribution for elementary widths.
- Determine the physical finite-channel replacement for the muon continuum phase space. For the tau total width, the electronic branching fraction remains an input; hadronic channels depend on [PMHadrons](../PMHadrons/REVIEW-AND-NEXT.md).
- A neutrino-decay prediction requires a physical channel and mass ordering. The corresponding cosmological propagation question is tracked in PMCosmology.
