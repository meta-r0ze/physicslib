# PMFlavor — open work

### The mixing functional forms

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹` evaluate derived
invariants, but which invariants and how they combine is supplied. This is the main derivation gap
of Paper IV. The structure behind the forms is derived (OVERVIEW, "Where the mixing comes from");
what remains:

* **The in-cycle mixings** (`HalfTurnMixing`, `HalfTurnAperture`, candidate). The half-turn
  refresh (the sign exchange) shared over a sector's type-preserving channels, `14` for quarks
  (`6` colour + `8` spinor) and `10` for leptons (`2` lepton-axis + `8` spinor), gives
  `s₁₂ = π/14` (quark amplitude) and `sin²θ₁₂ = π/10` (lepton probability), by the rule derived for
  the node (`KronSeries`: quark amplitude = admittance; Landauer: lepton probability =
  conductance). Derived pieces: the channel counts; `π` is Barbier's half-turn measure, a length
  along a boundary and an aperture through the refresh (`half_turn_measure`); the equal share is
  Closure (`equal_share_from_closure`). Remaining premise: the transfer crosses the refresh through
  its half-turn of directions (aperture) rather than along it. Data: `π/14` fits (`0.15σ`) and the
  rotation `sin(π/14)` is `>2σ` low; `π/10` fits JUNO and differs from the draft's `1/(2φ)` by
  `0.005`, which JUNO's full precision resolves.
* **The node-crossing coefficients.** `|V_ub| = 1/(2α⁻¹ + π)` is constructed (`VubSeriesPath`): the
  admittance of the two node legs and a unit boundary in series; the data's `m = 2` is the leg count.
  Its series premise follows from Conservation (`KronSeries`): a conserving link is a Laplacian, so
  eliminating the node is Kron reduction and the denominator `e − E` is the node's own conductance.
  The reactor's `3` is constructed (`ReactorConductance`). Open: `|V_cb| = (π + χ)/(α⁻¹ − Dπ)`. It is not a
  two-leg passive path (`VubSeriesPath.vcb_not_two_leg`: it needs a drive `≈ π + χ` over about one
  node impedance), and several single-impedance forms fit equally (`σ/(Z − 5π)`, `2π/(Z + 5π)`),
  so it needs a structural reason for the drive before data can test it. `VcbEnvelope` (candidate):
  with `env w = πw + χ` (Barbier boundary plus Descartes closures, as in `VevBoundary`), `Z_geo ≈
  env Δ` and `|V_cb| ≈ env 1 / env (Δ − D)`: one refresh tick's envelope against the cycle's free
  ticks, since each of the `D` frame rows is refreshed once per cycle (`RequirementRows`). The
  `c`-side hop is on the weak wall, which that refresh acts on; the `s`-side (`|V_ub|`) is on the
  spectator wall with a bare drive. Tests: the unit-tick drive is singled out (`1`, `χ`, `π`,
  `env 2` excluded by `>13σ`); `0` or `1` removed ticks are `>2σ` low. Open: derive that the hop
  amplitude is this divider.
* **The size of the parity breaking** that splits `s` from `c` (`ExchangeChirality`). Quarks: given
  by the two node-crossing constructions, a bare drive on the spectator wall (`VubSeriesPath`) and a
  refresh-tick drive on the weak wall (`VcbEnvelope`); it closes with them. Leptons: the deviation of
  `θ₂₃` from maximal (Paper IV's octant "running", no Lean statement). The data do not yet fix even
  its sign: NuFIT 6.0 normal ordering gives `sin²θ₂₃ = 0.561` without the Super-Kamiokande
  atmospheric data and `0.470` with it, so the paper's upper-octant `0.5748`
  (`PMNSGeometry.atmos_upper_octant`) is at risk. Upstream: the weak-wall versus spectator-wall
  asymmetry is what the carrier's axial current measures (slice-sign leakage, [action
  review](../PMAction/REVIEW-AND-NEXT.md)).
* **The CKM phase `δ = arctan(σ/χ)`.** With the paper's angles this puts the unitarity triangle's
  angle `α` at `89.5°`: `δ` is, to `0.5°`, the statement `α = π/2` (which gives `δ = 67.7°`,
  `γ = 67.7°`; HFLAV `α = 84.1 (+4.5/−3.8)°`, `γ = 66.4 (+2.8/−3.0)°`). A right angle at `α` is a
  modulus condition, `|V_cd V_cb|² = |V_ud V_ub|² + |V_td V_tb|²` (unitarity triangle with
  hypotenuse `V_cd V_cb*`), so it may follow from the network without a phase input. The simplest
  phase mechanism (the in-cycle coupling a rotation generator `i π/N`, node couplings real) puts the
  right angle at `γ` instead, which the data exclude. `CPQuarterTurn` tests the spinor route: a
  single-plane half-turn relating up and down would lift to a quarter turn (`plane_lift_sq`) and give
  `α = π/2` (`quadrature_pythagoras`), but the substrate's weak refresh is the full sign exchange
  (`WeakUniform.refresh_uniform`), which lifts to `±1` (`two_plane_lift_sq`). So that route is closed.
  Open: a source of the quadrature on the substrate; until then `δ` is supplied.
