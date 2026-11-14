# PMFlavor — open work

Status of the mixing forms (derivations in OVERVIEW, "Where the mixing comes from"): `|V_ub|` is
derived (`VubSeriesPath`, `KronSeries`); the reactor `sin²θ₁₃ = 3α` is constructed
(`ReactorConductance`); the CKM dressing `515/516` is derived (`DressingEvent`,
`DressingInheritance`). What remains:

* **The in-cycle mixings** (`HalfTurnMixing`, `HalfTurnAperture`, candidate): `s₁₂ = π/14` and
  `sin²θ₁₂ = π/10`. Derived: the channel counts, `π` as Barbier's half-turn measure, the equal share
  (Closure), the amplitude/probability rule (`KronSeries`, Landauer). Remaining premise: the
  transfer crosses the refresh through its half-turn of directions (aperture) rather than along it.
  `π/10` differs from the draft's `1/(2φ)` by `0.005`; JUNO's full precision resolves it.
* **`|V_cb|`** (`VcbEnvelope`, candidate): `env 1 / env (Δ − D)`, or the unit-source divider
  `env 1 / (env 1 + env (Δ − D))`; the data do not separate them. Remaining reading: a hop on the
  weak (refreshed) wall starts inside the node's cycle and crosses its free part once, instead of
  entering and leaving the node as the spectator-wall hop does.
* **`θ₂₃`** (the lepton `s`/`c` parity breaking; the quark one follows from the two node
  constructions). No construction yet, and the data do not fix the octant: NuFIT 6.0 normal
  ordering gives `sin²θ₂₃ = 0.561` without the Super-Kamiokande atmospheric data and `0.470` with
  it, so the draft's upper-octant `0.5748` (`PMNSGeometry.atmos_upper_octant`) is at risk. Upstream:
  the carrier's axial current (slice-sign leakage, [action review](../PMAction/REVIEW-AND-NEXT.md))
  measures the same weak-wall versus spectator-wall asymmetry.
* **The CKM phase** (supplied, `arctan(σ/χ)`). It is, to `0.5°`, the right angle `α = π/2`
  (`δ = 67.7°`; HFLAV `α = 84.1 (+4.5/−3.8)°`), which is the modulus condition
  `|V_cd V_cb|² = |V_ud V_ub|² + |V_td V_tb|²` (`CPQuarterTurn.quadrature_pythagoras`). Closed
  routes: an imaginary in-cycle coupling (right angle at `γ`, excluded by data) and a spinor quarter
  turn from the refresh (the derived refresh lifts to `±1`, `two_plane_lift_sq`). Open: a substrate
  source of the condition.
