# PMFlavor — open work

Status of the mixing forms (derivations in OVERVIEW, "Where the mixing comes from"): `|V_ub|` is
derived (`VubSeriesPath`, `KronSeries`); the reactor `sin²θ₁₃ = 3α` is constructed
(`ReactorConductance`); the CKM dressing `515/516` is derived (`DressingEvent`,
`DressingInheritance`). What remains:

Shared frame for all items (`LinkKronComparison`): flavour lives on the generation–class incidence
graph, three generation vertices and three class vertices, two legs per class. The quark mixings
are Kron reductions of it (per-class node crossings). The eigenvector link `B Bᵀ` is retired for
quarks (`LinkKronComparison`) and leptons (`LinkHierarchy`), so every remaining item is to be solved
on the network. Suggested order: the leg phases, then `|V_cb|`, then the aperture, then `θ₂₃`. Each
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
  * Settled (`ThirdGenerationMixing`): two real conserving sectors share `(1, 1, 1)` and their
    third row and column are `(1, 0, 0)` exactly (`zero_mode_unmixed`); that is the data's leading
    order, so `|V_ub|`, `|V_cb|` are first-order effects of what lifts the zero mode differently in
    the two sectors, `⟨v_k, P w⟩/λ_k`, not couplings read off directly. Next: identify `P`. Two
    candidates in the library: a flux (`LinkFlux`) and a non-conserving leak. Test each against
    the gaps `in_cycle_spectrum` gives (`3α/2` for the node-class generation, `a + α/2` for the
    in-cycle pair): `VubSeriesPath`'s `1/(2α⁻¹ + π)` must come out as `⟨v_k, P w⟩/λ_k` with
    `P` built from the same legs and boundary, and the same `P` must give `|V_cb|`. If the
    required `P` has no library source, the amplitude-is-admittance premise of `VubSeriesPath` is
    the error; record it.
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
  Suggested attack: the eigenvector link no longer supplies a `θ₂₃` (`LinkHierarchy`), so it has to
  come from the lepton legs of the network: the one-leg reactor passage (`ReactorConductance`) and
  the in-cycle aperture. On the incidence graph the `μ` and `τ` generations reach the reference
  through different class vertices (`s` and `c`), so the `μ`–`τ`-asymmetric factor `Theta23Wall`
  requires can be the same `s`/`c` vertex difference that the `|V_cb|` item finds. Do `|V_cb|`
  first and carry its `c`-vertex terminal to the lepton side; test against both NuFIT values
  (`2 sin²θ₂₃ − 1 = +0.122` or `−0.060`).
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
  Done (`LinkFlux`): with complex legs the reduction keeps one invariant per sector, the flux of the
  reduced triangle. A leg phase set by the leg's wall (`GenerationWalls.side`) gives flux `ū⁶`
  (`flux_cyclic`); exchanging the wall names conjugates it (`flux_swapped`, `J → −J`); the `μ`–`τ`
  swap reverses the orientation (`swap_reverses_orientation`), so a `Z₂`-invariant pattern conserves
  CP. The sign of `δ` is the wall-naming convention, which is the same orientation input
  `ReferenceFlavour.column2_difference_conj` leaves open, now located.
  Open: the size. Suggested attack:
  * Find a substrate source for a wall-dependent leg phase `θ` (flux `6θ`, CP-conserving iff
    `θ ∈ (π/6)ℤ`). The walls are the two `D₄` copies of opposite chirality and the inter-wall
    hop is `hop ⊗ Y` (`PMAction.WallExchange`); look for a phase in how a single-wall class hop
    enters that hop, before considering any angle. Do not reuse the closed routes in
    `CPQuarterTurn`: a refresh phase lifts to `±1`, and an imaginary in-cycle coupling puts the
    right angle at `γ`.
  * Moduli and phase are not independent tests: `J` vanishes for uniform legs in each sector (all
    moduli equal), so the CP size needs the leg moduli too. Do `|V_cb|` (which fixes how the legs
    differ between sectors) before testing a `θ`.
  * Test once both exist: `CPQuarterTurn.quadrature_pythagoras` (target `α = π/2`, HFLAV
    `84.1 (+4.5/−3.8)°`) and `|V_td| = 0.0086 ± 0.0002`. If no wall-side `θ` gives `α` in range
    with the derived moduli, the wall-side phase route is closed; record it.
  * The same flux with the lepton legs is the candidate PMNS phase.

Working notes for the next session: there is no Lean toolchain in the device shell, so write
proofs to be deterministic and ask Kate for `./build.sh fast PMFlavor`. Avoid `simp` on a
transposed matrix literal or a product of three literals; name the intermediate literal and use
`rfl` for literal identities (`LinkKronComparison.Lcg_eq_transpose`, `Lgc_mul_inv`). Numerical
scans belong outside Lean and are labelled as such here.

