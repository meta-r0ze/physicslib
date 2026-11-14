# PMFlavor — open work

Status of the mixing forms (derivations in OVERVIEW, "Where the mixing comes from"): `|V_ub|` is
derived (`VubSeriesPath`, `KronSeries`); the reactor `sin²θ₁₃ = 3α` is constructed
(`ReactorConductance`); the CKM dressing `515/516` is derived (`DressingEvent`,
`DressingInheritance`). What remains:

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
* **`|V_cb|`** (`VcbEnvelope`, candidate formula): `env 1 / env (Δ − D)`, or the unit-source
  divider `env 1 / (env 1 + env (Δ − D))`; the data do not separate them, and the unit drive is
  singled out among simple drives. The supporting reading (`D` refresh ticks per cycle, `Δ − D`
  free) is not supported by the library: rows are assigned whole (`RequirementRows`, no clock-slot
  variable) and weak reaches all `43` clock addresses (`WeakLocality`). Next: trace a weak-wall
  input through the actual refresh with its generation label (`ExchangeChirality`), find the first
  operation that changes the label and the source and sink terminals, then Kron-reduce; the same
  convention on the spectator side must recover `VubSeriesPath`. If the weak update acts within
  each generation, the drive is the inter-wall link's and refresh placement does not fix `|V_cb|`.
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
  angle at `γ`, excluded). Next: compute the quartet
  `tr(P_u P_d P_t P_b) = V_ud V_td* V_tb V_ub*` from spectral projectors of the up and down wall mass
  operators, and ask whether a constraint on the pair forces `Re = 0` with `Im ≠ 0`; one admissible
  example with `Re ≠ 0` disproves exact quadrature from the current constraints.
