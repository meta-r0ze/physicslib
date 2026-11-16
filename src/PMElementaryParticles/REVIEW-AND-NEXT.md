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

**The wire in six-pillar terms (2026-11).** A protocol over the wire is a PM system, and the open
flavour numbers sit in the pillars the papers usually leave out:
| Pillar | On the wire | Status |
|---|---|---|
| Capacity | three label states; node conductance | derived (`GenerationSector`, `KronSeries`) |
| Map | label states → the protocol's persisting states (`U`, the mass basis) | open: the protocol-level `U` |
| Protocol | up, down, `e`, `ν` as information over the wire | species content derived (`CarrierRepresentation`) |
| Governor | the stationary reference (`δ_R = 0`), the weak refresh | derived (`ReferenceDetuning`, `CarrierActions`) |
| Toll | node passage `α` (`k/K = α/2`), the jump `1/(2α⁻¹ + π)` | derived, reading of rates open (`CertainTransferRate`) |
| Margin | the other wall's detuning `δ_O`, per protocol (down `64.6 k_f`, `e` `18.8 k_f`, up `11.2 k_f` from the lightest ratios) | open |
PMFlavor's three label changes are PM's three transfer modes (`PersistenceMechanics.InformationTransfer`:
boundary conduction, capacity promotion, coordinate jump = `TransferGraph.mode`). Lead: use what
`PersistenceMechanics` says about Margin (`DecayChannel`, `MarginCorrection`) and about how a system's
margin is selected, to fix `δ_O` per protocol instead of reading it off a mass ratio.

**Margin, first pass (2026-11).** From Paper I: Margin is Finiteness's defense, "reserves and
operating tolerances that absorb disturbances without leaving the viable range"; with no Margin a
system sits at criticality and fails to any perturbation. On the wire: the reference's wall sits at
`δ_R = 0` (Governor, stationary), and a wire with no detuning on the other wall has the reversed
ordering (`PMAction.UndetunedWall`): PM's no-margin failure, so `δ_O ≠ 0` is Margin's existence.
Size: in units of the vector flip, `LightPairTexture`'s `δ(1 − t²) = t` makes the Margin and the Map
overlap one number, `δ_O ≈ tan θ₁₂ = √(m₁/m₂)`: down `0.236`, `e` `0.069`, up `0.041`. Quick test of a
minimal-action rule (detuning cost `∝ δ²`, disturbance hazard `∝ (load/δ)²`, so `δ ∝ √load`): needs
loads `33 : 2.8 : 1` (down : `e` : up); no protocol quantity tried has those ratios (`Q²`, `Y_R²`).
Open: Paper I's selection with protective expenditure (`4_minimum_action`, cumulative hazard
`H_i = ∫ β_i Z_net dt`) applied to the wire, with the protocol's own disturbance identified.
**Margin as the minimum to persist (Kate, 2026-11).** `δ_O` is the smallest detuning at which the
protocol's states still persist. On the corrected wire (numerical): at `δ_O = 0` the two heavier
states are degenerate (`Kk`, `Kk`; `UndetunedWall.undetuned_masses_matching`); they split as
`√(1 + u²) Kk` and `≈ Kk` (`u = δ_O/k_f`), the third stays `≈ k²`. So the threshold to find is the split
at which two states count as distinct persisting states. Instant fails: a common absolute gap
(`m_b − m_s`, `m_t − m_c`, `m_τ − m_μ` are `4.1`, `171`, `1.7` GeV). Candidates to state and test: the
split reaching orthogonality within the maintenance cycle (Toll's Margolus–Levitin bound,
`ΔE · T ≥ π/2`, with `T` the clock period); the split exceeding the protocol's own disturbance (its
carrier coupling to the third state). Each needs the protocol's time or disturbance scale.
Tried: "smallest `δ_O` keeping each persisting state mostly one label" (minimize the largest
off-diagonal `|U|`): best at `δ_O ≈ k_f` (`0.004`), the same for every protocol, with heavy/middle
`≈ 1.4`: no hierarchy and no protocol dependence. Excluded. The data's margins are large
(`δ_O/k_f = 11`–`65`), where the heavy/middle ratio is `≈ δ_O/k_f`; so the threshold is set by a
requirement that the heaviest state stand clear of the other two, scaled per protocol.
Further tries (2026-11): (i) "margin = the amplitude of the charged-current change the protocol must
survive": down's margin `0.236 ≈ κ₀`, up's `0.041 ≈ |V_cb|`; but these are the GST relation and the
known `√(m_u/m_c) ≈ |V_cb|` coincidence restated, not a derivation, and the lepton margin `0.069` has
no `J` partner. (ii) Margolus–Levitin within a protocol's maintenance period: up and down share their
maintenance (weak, hypercharge, colour refreshes) yet their margins differ by `6×`. Excluded as
stated. What is missing is PM's characteristic perturbation of a protocol on the wire; the library
does not yet name it.
**Information-theory reading (Paper I's mapping: channel capacity, codebook, framing, power, overhead,
link margin), 2026-11.** It gives operational definitions to test:
- *Margin = link margin.* `u = δ_O/k_f` is a signal-to-noise ratio: the other wall's flip (signal)
  over the spinor carrier's flip (noise, what couples a label to its neighbours). "Minimum to
  persist" becomes: the SNR at which the channel just carries the rate `R_p` the protocol must
  sustain, `log₂(1 + u_p) = R_p`. From the data's margins `R_p = 6.04` (down), `4.31` (`e`), `3.61` (up)
  bits. Test: derive `R_p` from the protocol's content and predict `u_p = 2^{R_p} − 1`. Not done; no
  count is chosen to match.
- *Map = codebook.* The persisting states are codewords on the three label states; `t` is cross-talk.
  `LightPairTexture` says cross-talk squared equals the power (mass) ratio of the two codewords.
- *The CKM is the transfer channel between two codebooks.* With PDG magnitudes and a uniform input,
  it carries `I = 1.38` bits of the `log₂ 3 = 1.585` (loss `0.21` bits per transfer).

**What we know (2026-11), in one place.**
1. Wire: rows `(K, k, k)`, other-wall shift `(k, K, k)`: the vector carrier sits on the light pair
   (`PMAction.GenerationCurrent`, `UndetunedWall.undetuned_masses_matching`).
2. Map and Margin are one number per protocol: `δ(1 − t²) = t`, `tan θ₁₂ = √(m₁/m₂)` (`LightPairTexture`).
3. The `β` event is coherent (data, PMAction REVIEW).
4. Margins from the lightest ratios: `u = δ_O/k_f` = `64.6` (down), `18.8` (`e`), `11.2` (up); with them
   down and `e` predict their second ratio within `10%`, up misses by `12×`.
5. Up and down share colour and maintenance; only hypercharge (and the doublet sign) tells them apart.
6. Cabibbo wants a quarter turn between the up and down cycle phases.
7. Information-theory reading: `R_p = log₂(1 + u_p)` = `6.04`, `4.31`, `3.61` bits (down, `e`, up).

**Brainstorm: what is the rate `R_p` a protocol must sustain? (quick checks against the ordering
down > `e` > up, nothing tuned).**
| Candidate | Values (down, `e`, up) | Ordering |
|---|---|---|
| `log₂` multiplet size (right sector: 3, 1, 3) | 1.58, 0, 1.58 | up = down: fails |
| repair events (`RootRepairRule`) | equal for up, down | fails |
| `|Y_R|` (2/3, 2, 4/3) | | `e` > up > down: fails |
| `|Q|` (1/3, 1, 2/3) or `1/|Q|` | | fails |
| hypercharge response `(Y_R/2)²` | | fails |
| doublet sign (lower: down, `e`; upper: up) plus colour | | down, `e` high, up low: matches |
Additive bits (independent channels add): with colour adding `log₂ 3 = 1.585` bits, `R_d − R_e = 1.73`
(within the `±0.15` from the margins' `10%`). The lower-minus-upper term is then `≈ 2.3–2.4` bits (from
`R_e − R_ν` and `R_d − R_u`), not yet derived. Prediction, conditional: `R_ν = R_u − log₂ 3 = 2.02`,
`u_ν ≈ 3.07`, which on this wire gives a strongly hierarchical, weakly mixed neutrino protocol: in
tension with the large PMNS angles unless neutrinos read the wire differently (Majorana, on-axis
one-leg readout). Status: a pattern with one passing check, not a derivation. Next: derive the
lower/upper term from the doublet structure (the refresh acts on the sign, `CarrierActions.weak`), and
settle how a neutral protocol reads the wire.

**Step 1: the doublet term (2026-11).** Target: lower minus upper `≈ 2.36 ± 0.15` bits (from `R_d − R_u`
and `R_e − R_u + log₂ 3`), equivalently a factor `≈ 5.4 ± 0.8` in `1 + u`. Facts: the reference sits
on the upper, neutral member (`ν`, `PMConstants.ReferenceStabilizer`, `ReferenceMasses`); the doublet
index is the carrier's sign (`CarrierRepresentation`), and the weak refresh negates every carrier of
the reference's sector (`CarrierActions.weak`), which exchanges the doublet positions there. So the
term separates protocols on the reference's doublet position (up, `ν`) from displaced ones (down, `e`).
Quick counts: one sign bit (`1`), signs on both walls (`2`, `2.4σ` low), charge or hypercharge
displacement squared (wrong ordering: up carries more charge than down yet needs less margin).
None derived. Open: how the refresh's per-tick exchange of doublet positions costs a displaced
protocol information, counted from `CarrierActions.weak` and the maintenance ledger.
Run: against the reference, the refresh cannot tell the positions apart. It negates every carrier of
its sector uniformly (`PMConstants.WeakUniform.refresh_uniform`), so every unit state has flag
`‖φ − (−φ)‖²/4 = 1`, and every protocol state is orthogonal to the reference carrier. Excluded as the
source of the doublet term.

**The form of the minimum margin (2026-11).** The library's own pillar theorems fix it:
`PMSubstrate.Pillars.map_maintains` (correction toward a retained reference with gain `k` keeps the
deviation within `W/k` for disturbances `≤ W`) with `margin_iff` (Margin is distance to the non-viable
set) give `PMSubstrate.MinimumMargin.persists_of_margin`: the minimum margin to persist is `W/k`. On
the wire, with the spinor flip as the disturbance, `δ_O/k_f = 1/k`: the correction gains are `0.0155`
(down), `0.053` (`e`), `0.089` (up). The question becomes what sets a protocol's correction gain.
Quick checks: gain `∝ (Y_R/2)²` gives the ordering `e` > up > down (data: up > `e` > down); gain `∝ |Y_R|`
gives `e/down = 3` (data `3.4`) but `up/down = 2` (data `5.8`). Neither fits.

**The reference as a PM system, and the gain as the governor's reach (2026-11).** The reference sits at
`δ_R = 0`: zero Margin, fragile by `Pillars.fragility`. It persists because the weak refresh repairs
it every tick: Paper I's protective architecture (`4_minimum_action`, "Margin and Governor can
increase expenditure while reducing failure exposure"), Governor standing in for Margin. If the same
governor corrects the protocols, a protocol's gain is how strongly the reference's maintenance
reaches it. Checks against the gains (up `0.089` > `e` `0.053` > down `0.0155`):
- *Shared attributes with the reference* (`ν`: upper position, lepton axis): up shares the position,
  `e` the axis, down neither. The ordering matches. Multiplicatively, position `×5.75`, axis `×3.4`;
  `ν` (both) would have gain `≈ 0.30`, `u_ν ≈ 3.3` (the same content as the additive-bits estimate
  `3.07`). But "same position as the reference" is not geometric for up versus down
  (`DoubletReflection`: a colour reflection fixes the reference carrier and exchanges them), so it
  needs a charge.
- *Charges as distance from the reference*: `|Q − Q_ν|` (`2/3`, `1`, `1/3`), `|Y_R − Y_{ν R}|` (`4/3`, `2`,
  `2/3`), right-handed `Z` couplings (`0.154`, `0.231`, `0.077`): all order `e` above up. Fail.
So the ordering points at shared attributes with the reference, and the up/down part of it has no
source yet that respects `DoubletReflection`.

**Bookkeeping correction (2026-11, PMAction REVIEW).** The other wall's vector carrier sits on the
light pair (`PMAction.GenerationCurrent.edge_carrier`), not between the heavy label and a light one.
Results below that used the old assignment: the `WireLightSplit` relation test and its recorded
species numbers (withdrawn; that block no longer describes the wire), and the "protocol-level `U`,
first test" (moot: with the corrected assignment the 2–3 rotations are `≲ 4·10⁻⁴` and `|V_cb|` comes
from `J`). Still valid: `UpDownWire.product_equal` (the determinant is symmetric) and its spectra
statement (re-checked: equal iff `|k_s| = |k_c|`). New, with the corrected wire (PMFlavor REVIEW,
"Redone"): fixing each protocol's `δ_O` by its lightest ratio, down and charged leptons predict their
second ratio within about `10%` (`m_s/m_b = 0.0163` vs `0.0185`, `m_μ/m_τ = 0.053` vs `0.0595`), up
misses by `12×` (`m_c/m_t = 0.089` vs `0.0074`). So down and leptons read the wire's singular values
roughly directly; up does not.

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
