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
  `NodeElimination` derives this for the node; the in-cycle case needs the share `π/N` shown to
  be a through weight (Landauer, as in `PMConstants.HandoffAdmittance`). Upstream tools do not yet
  supply it: the event-law link cost and the branch pulse are quadratic in the angle
  (`PMAction.LinkExpansion`: `ε²‖θφ‖²`; `HandoffAdmittance`: `sin² t`), so a share linear in `π/N`
  needs a rate per channel rather than a pulse. The closest upstream item is the routing histories
  and rates of the [elementary-particle review](../PMElementaryParticles/REVIEW-AND-NEXT.md).
* **The node-crossing coefficients.** `|V_ub| = 1/(2α⁻¹ + π)` is constructed (`VubSeriesPath`): the
  admittance of the two node legs and a unit boundary in series; the data's `m = 2` is the leg count.
  The reactor's `3` is constructed (`ReactorConductance`). Open: `|V_cb| = (π + χ)/(α⁻¹ − Dπ)`. It is not a
  two-leg passive path (`VubSeriesPath.vcb_not_two_leg`: it needs a drive `≈ π + χ` over about one
  node impedance), and several single-impedance forms fit equally (`σ/(Z − 5π)`, `2π/(Z + 5π)`),
  so it needs a structural reason for the drive before data can test it. Candidate from the node
  impedance itself: `Z_geo = πΔ + χ + …` is a causal envelope's boundary `πw` (Barbier) plus its
  `χ` closures (Descartes) at width `w = Δ` (`PMSubstrate.Impedance`, `PMConstants.VevBoundary`).
  Writing `Z(w) = πw + χ`, the drive `π + χ` is `Z(1)`, a unit-width envelope, and
  `Z_geo − Dπ ≈ Z(Δ − D)`, so `|V_cb| ≈ Z(1)/Z(Δ − D)`: a divider between two envelopes. Open: why
  the `c`-side hop drives with a unit envelope and why `D` of the `Δ` widths drop out.
* **The size of the parity breaking** that splits `s` from `c` (`ExchangeChirality`): large for
  quarks (`|V_ub|/|V_cb| ≈ 0.09`, mostly a drive ratio, `VubSeriesPath.vcb_not_two_leg`), small for
  leptons (`θ₂₃` near maximal; Paper IV's octant "running" is this breaking and has no Lean
  statement). Upstream: the same weak-wall versus spectator-wall asymmetry is what the carrier's
  axial current measures (the slice-sign leakage in the [action review](../PMAction/REVIEW-AND-NEXT.md));
  its many-slice limit may give the size.
