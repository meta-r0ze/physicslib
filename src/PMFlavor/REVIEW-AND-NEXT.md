# PMFlavor — open work

Status of the mixing forms (derivations in OVERVIEW, "Where the mixing comes from"): `|V_ub|` is
derived (`VubSeriesPath`, `KronSeries`); the reactor `sin²θ₁₃ = 3α` is constructed
(`ReactorConductance`); the CKM dressing `515/516` is derived (`DressingEvent`,
`DressingInheritance`). What remains:

Shared frame for all items (`LinkKronComparison`): flavour lives on the generation–class incidence
graph, three generation vertices and three class vertices, two legs per class. The quark mixings
are Kron reductions of it (per-class node crossings). The eigenvector link `B Bᵀ` is retired for
quarks and is a lepton candidate only. Suggested order: the lepton label question (cheapest, it can
kill or keep the candidate), then the leg phases, then `|V_cb|`, then the aperture. Each
"Suggested attack" below is a candidate route with its test, not a result.

* **The in-cycle mixings** (`HalfTurnMixing`, `HalfTurnAperture`, candidate): `s₁₂ = π/14` and
  `sin²θ₁₂ = π/10`. Derived: the channel counts, `π` as Barbier's half-turn measure, the equal share
  (Closure's label-blind pricing, `equal_share_from_closure`, which assumes invariance under every
  permutation; the physical type-preserving symmetries keep the vector and spinor channels in
  separate orbits, so the equality across orbits rests on label-blindness, not symmetry), the
  amplitude/probability rule (`KronSeries`, Landauer). Remaining premise: the
  transfer crosses the refresh through its half-turn of directions (aperture) rather than along it.
  Test: split the half-turn into two arcs with fixed generation terminals; an aperture adds them in
  parallel, a length in series. This needs the directional contributions to be separately
  addressable, which the endpoint map `v ↦ −v` (`WeakUniform`) alone does not supply.
  `π/10` differs from the draft's `1/(2φ)` by `0.005`; JUNO's full precision resolves it.
  Suggested attack:
  * Put the in-cycle pair on the incidence network. The vector class vertex has two legs like the
    others, so the convention that gave `|V_ub|` (mixing amplitude = Kron-reduced coupling,
    `two_leg_from_incidence`) gives `s₁₂ = g_v/2` for a vector leg `g_v`. Check whether
    `HalfTurnMixing`'s equal share is this `g_v/2` with no extra factor. If the `2` has to be put
    in or taken out by hand, either the aperture reading or the amplitude convention is wrong, and
    `|V_ub|` (data-fixed `m = 2`) says which.
  * The separately addressable directions the parallel/series test needs may be the `6`
    axis-free vector displacements (`ExchangeAxis.vector_free`): they are distinct carrier
    displacements with the same generation terminals. Build the six-edge network between the two
    generations, show whether Conservation makes them parallel edges (aperture) or a chain
    (length), and compare with the `14` and `10` of `π/14`, `π/10`. Falsifier: a count other than
    the ones `HalfTurnMixing` derives.
* **`|V_cb|`** (`VcbEnvelope`, candidate formula): `env 1 / env (Δ − D)`, or the unit-source
  divider `env 1 / (env 1 + env (Δ − D))`; the data do not separate them, and the unit drive is
  singled out among simple drives. The supporting reading (`D` refresh ticks per cycle, `Δ − D`
  free) is not supported by the library: rows are assigned whole (`RequirementRows`, no clock-slot
  variable) and weak reaches all `43` clock addresses (`WeakLocality`). Next: trace a weak-wall
  input through the actual refresh with its generation label (`ExchangeChirality`), find the first
  operation that changes the label and the source and sink terminals, then Kron-reduce; the same
  convention on the spectator side must recover `VubSeriesPath`. If the weak update acts within
  each generation, the drive is the inter-wall link's and refresh placement does not fix `|V_cb|`.
  Suggested attack:
  * `|V_ub|` and `|V_cb|` cross different class vertices (`s` and `c`), not one shared node
    (`shared_node_three_legs`). So the factor `≈ 10` is a difference between those two vertices.
    `ExchangeChirality` says which: the weak current couples to one of them. Model that as a third
    terminal on the `c` vertex (source or sink of the weak-wall hop) and Kron-reduce the
    three-terminal vertex. A two-leg vertex gives a series admittance; a three-terminal one gives a
    divider, which is the shape of both `VcbEnvelope` candidates.
  * A terminal to ground is a diagonal term, which `diagonal_breaking_not_network` shows is not a
    leg change. So first settle whether Conservation allows it: the reference would have to be the
    ground that absorbs the current. If Conservation forbids a shunt, the divider reading is closed
    and `|V_cb|` must come from unequal legs at the `c` vertex instead.
  * Tests: the same construction with the terminal removed must return `VubSeriesPath` exactly;
    it must not dress leptonic or neutral currents (`DressingInheritance`); the value must sit in
    `0.0411 ± 0.0012`; and with the right-angle condition it must keep `|V_td|` in
    `0.0086 ± 0.0002`.
* **`θ₂₃`** (the lepton `s`/`c` parity breaking; the quark one follows from the two node
  constructions). No construction yet, and the data do not fix the octant: NuFIT 6.0 normal
  ordering gives `sin²θ₂₃ = 0.561` without the Super-Kamiokande atmospheric data and `0.470` with
  it, so the draft's upper-octant `0.5748` (`PMNSGeometry.atmos_upper_octant`) is at risk. `Theta23Wall`: the
  normalized asymmetry `(W_μ − W_τ)/(W_μ + W_τ)` is `2 sin²θ₂₃ − 1` (NuFIT: `+0.122` or `−0.060`),
  and with the factorized current `P_L ⊗ G` a wall factor common to both readouts cancels
  (`common_wall_cancels`). So a construction must supply a `μ`–`τ`-asymmetric generation factor or
  wall overlaps correlated with the readout (`wall_only`); a weak-wall versus spectator-wall
  asymmetry shared by both generations, such as the carrier's axial current ([action
  review](../PMAction/REVIEW-AND-NEXT.md)), does not move `θ₂₃` by itself.
  Suggested attack: the eigenvector-link item at the end of this file is the only construction that
  currently outputs a `θ₂₃`. `brokenLinkB ε` is a `μ`–`τ`-asymmetric generation factor of the kind
  `Theta23Wall` requires, so check that its asymmetry is the `(W_μ − W_τ)/(W_μ + W_τ)` of
  `Theta23Wall` and not a common wall factor. If that item's label test fails, `θ₂₃` needs the
  lepton legs of the network instead (one-leg reactor passage plus in-cycle aperture), which so far
  give no `θ₂₃`.
* **The CKM phase** (supplied, `δ = arctan(σ/χ) ≈ 68.2°`). It puts the triangle angle `α` at
  `89.5°`; exact `α = π/2` would give `δ = 67.7°` (in the library's convention,
  `cos δ = c₁₂c₂₃s₁₃/(s₁₂s₂₃)`; HFLAV `α = 84.1 (+4.5/−3.8)°`). The right angle is the modulus
  condition
  `|V_cd V_cb|² = |V_ud V_ub|² + |V_td V_tb|²` (`CPQuarterTurn.quadrature_pythagoras`). Equivalently
  it predicts `|V_td| = 0.00858` (data `0.0086 ± 0.0002`), conditional on the other magnitudes,
  including the candidate `|V_cb|`. Closed routes (`CPQuarterTurn`): an
  imaginary in-cycle coupling (right angle at `γ`, excluded); a spinor quarter turn from the refresh
  (the derived refresh lifts to `±1`); route non-interference (the `u` and `t` routes share
  endpoints, so they interfere); maximal `|J|` with the derived angles fixed (gives `δ = π/2`, right
  angle at `γ`, excluded). The current link constraints do
  not decide it: any mixing, any `δ`, is realized by Hermitian positive links
  (`MassMixing.positive_masses_allow_any_mixing`), and the structural constraints fix moduli, not
  the phases of the link entries. Open: a constraint on the phases of the inter-wall link `Y`.
  Suggested attack:
  * Phases live on the legs of the incidence graph. Kron reduction of a Hermitian (magnetic)
    Laplacian keeps every series modulus and passes the leg phases to the reduced couplings, which
    matches "the constraints fix moduli, not phases". Prove that first: `kron_schur` with complex
    legs `t₁, t₂`, class self-term `|t₁| + |t₂|`, reduced coupling `−t₁ t̄₂ / (|t₁| + |t₂|)`.
  * One sector has a single gauge-invariant phase: the flux around the hexagon, which after
    reduction is `arg(Y₀₁ Y₁₂ Y₂₀)`. A CKM phase needs two sectors with different flux. The
    library has exactly two balanced incidence conventions, exchanged by swapping the wall names
    (`PMConstants.GenerationWalls`), and they are cyclic in opposite senses. Candidate: the up and
    down sectors are the two conventions, and `δ` is their relative flux. Compute that flux from
    the glue-class structure (the cyclic `side g c = (c = g + 1)` orientation) before looking at
    data.
  * Test: feed the reduced couplings with that flux into `CPQuarterTurn.quadrature_pythagoras`.
    The target is `α = π/2`; the data are HFLAV `α = 84.1 (+4.5/−3.8)°` and `|V_td|`. Do not
    reuse the closed routes: the flux here comes from the incidence orientation, not from the
    refresh (which lifts to `±1`) or an imaginary in-cycle coupling. If the two conventions give
    equal flux, this route is closed too; record it.
  * `protected_overlap_phase_blind` is the lepton version of the same statement (leg phases leave
    the protected overlap alone), so one flux computation serves both sectors.
* **The eigenvector link as a lepton candidate** (`LinkKronComparison`). It is retired for quarks
  (a fixed `|V|² = 1/4` entry). For leptons the fixed entry is a test. The numbers below are
  computed numerically outside Lean, with `sin²θ₁₃ = 3α` and the candidate `sin²θ₁₂ = π/10` as
  inputs.
  * Real link (no phases, so `δ_CP ∈ {0, π}`): the `1/4` entry gives `sin²θ₂₃ = 0.5575`
    (`|U_τ1|`, `δ_CP = π`), `0.4425` (`|U_μ1|`, `0`), `0.5411` (`|U_μ2|`, `0`) or `0.4589`
    (`|U_τ2|`, `π`); the four other sign branches (`0.086`, `0.268`, `0.732`, `0.914`) are outside
    the NuFIT 6.0 `3σ` range. Each allowed branch is realized by some `(δ, ε)`, e.g. `0.5575` at
    `(1.944, 6.243)` and `(−3.421, 16.119)`. All four contradict the sum rule `|U_μ2| = |U_τ2|`
    (`ReferenceFlavour`) and the library's `J ≠ 0`.
  * Legs with phases (`protected_overlap_phase_blind`) and the sum rule kept: the `1/4` must sit in
    column 1, giving `sin²θ₂₃ = 0.5873`, `cos δ_CP = −0.877` (`δ_CP = 208.7°` on the `sin δ < 0`
    branch, `|J| = 0.0159`) for `|U_τ1| = 1/2`, or the mirror `0.4127`, `cos δ_CP = +0.877` for
    `|U_μ1| = 1/2`. Against NuFIT 6.0 `3σ` (arXiv:2410.05380): the first has `|U_μ3| = 0.758`,
    `|U_τ3| = 0.635`, inside the ranges without Super-Kamiokande atmospheric data
    (`0.649–0.764`, `0.628–0.746`) and `0.002` outside with it (`0.652–0.756`, `0.637–0.743`); the
    mirror is outside both (`|U_μ3| = 0.635`). A realization exists (`δ, ε ≈ 4.57, 3.97` with two
    leg phases), so this is four parameters meeting four numbers, not a derivation.
  * Open: which mass labels the two protected states carry (this picks the branch), and what
    fixes `δ`, `ε` and the leg phases. At the real solution points the link eigenvalue order does
    not follow the mass order of the labels the angles require (the electron row is the middle
    eigenvalue at `(1.944, 6.243)`), so a monotone eigenvalue-to-mass map fails there; not yet
    checked for the phased case.
  * Open: the network has no `δ, ε`. The lepton-side legs that would replace them (one-leg
    reactor passage, in-cycle aperture) do not yet give a `θ₂₃`, so the two lepton descriptions
    are not reconciled.
  Suggested attack:
  * Labels first. `PMAction.WallSeesaw` gives light masses `δ²/σᵢ(Y)`, so the eigenvalue order
    fixes which rows and columns the protected states are. Enumerate the orders for the phased
    solutions and keep only those matching `e < μ < τ` and a neutrino ordering. If none survives,
    the eigenvector link is retired for leptons too; record that and delete this item.
  * Bounds already known by hand (worth one small Lean lemma each): as `δ, ε → 0` the two sectors
    share the democratic state and the matrix has an entry `1`; as `δ, ε → ∞` it has an entry `0`.
    Both are excluded by data, so `δ, ε` are of order one in leg units and cannot be small node
    conductances `∝ α`. A reading of `δ, ε` as one-leg shunts to the reference is therefore closed
    unless the unit is changed.
  * The sum rule decides real versus phased. Check whether `ReferenceFlavour`'s `|U_μ2| = |U_τ2|`
    is derived independently of the link. If it is, the four real branches are dead and the single
    prediction is `sin²θ₂₃ = 0.5873`, `δ_CP = 208.7°`, to be tested against the next global fit
    (it is `0.002` outside the with-SK `3σ` range now).
  * Then remove the freedom: the two leg phases should be the incidence flux of the CKM-phase item,
    leaving `δ, ε`. Two inputs for `θ₁₂, θ₁₃` is still a fit; it becomes a derivation only if a
    cost (`RelativeFrameCost`, `TransferWorkLaw`) or Closure fixes them.

Working notes for the next session: there is no Lean toolchain in the device shell, so write
proofs to be deterministic and ask Kate for `./build.sh fast PMFlavor`. Avoid `simp` on a
transposed matrix literal or a product of three literals; name the intermediate literal and use
`rfl` for literal identities (`LinkKronComparison.Lcg_eq_transpose`, `Lgc_mul_inv`). Numerical
scans belong outside Lean and are labelled as such here.

