# PMFlavor — open work

### The mixing functional forms

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹` evaluate derived
invariants, but which invariants and how they combine is supplied. This is the main derivation gap
of Paper IV. The structure behind the forms is derived (OVERVIEW, "Where the mixing comes from");
what remains:

* **The in-cycle mixings (`HalfTurnMixing`, candidate).** A half-turn (the sign-exchange refresh)
  shared over the type-preserving channels gives `π/14` for quarks (`6` colour + `8` spinor) and
  `π/10` for leptons (`2` lepton-axis + `8` spinor); the supplied `1/(2φ)` is exactly `sin(π/10)`.
  Data: the quark share must be the generator element `π/14` (the rotation `sin(π/14)` is `>2σ`
  low); the lepton probability fits either `π/10` or `sin(π/10)`. Open: derive why the share is the
  generator element and is read as an amplitude for quarks and a probability for leptons. That
  fixes the solar prediction (`π/10 = 0.3142` versus `0.3090`). One rule would cover all four
  constructed mixings: each is a leg weight `w` (node `α`, in-cycle `π/N`); quarks reach the
  junction by two legs, so `w` is their amplitude (`|V_ub|, |V_cb| ∝ α`, `s₁₂ = π/14`), and
  lepton-axis states by one, so `w` is their probability (`sin²θ₁₃ = 3α`, `sin²θ₁₂ = π/10`).
  For the node this is now derived: quark couplings are Kron-reduced admittances of a conserving
  link (`KronSeries`), and the lepton side is a node passage whose probability is its conductance
  (Landauer, `PMConstants.HandoffAdmittance`). `HalfTurnAperture` reconciles the in-cycle case with
  Ohm's geometric law (conductance = aperture / length): along a Barbier boundary `π` is a length
  (impedance, the node-crossing paths), through the half-turn refresh it is an aperture shared by
  the `N` channels in parallel (admittance `π/N`). Remaining premise: the refresh's half-turn is
  such an aperture, shared equally. This selects `sin²θ₁₂ = π/10` over the supplied `1/(2φ)`. Upstream tools do not yet
  supply it: the event-law link cost and the branch pulse are quadratic in the angle
  (`PMAction.LinkExpansion`: `ε²‖θφ‖²`; `HandoffAdmittance`: `sin² t`), so a share linear in `π/N`
  needs a rate per channel rather than a pulse. The closest upstream item is the routing histories
  and rates of the [elementary-particle review](../PMElementaryParticles/REVIEW-AND-NEXT.md).
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
