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
  angle at `γ`, excluded). The current link constraints do
  not decide it: any mixing, any `δ`, is realized by Hermitian positive links
  (`MassMixing.positive_masses_allow_any_mixing`), and the structural constraints fix moduli, not
  the phases of the link entries. Open: a constraint on the phases of the inter-wall link `Y`.
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

