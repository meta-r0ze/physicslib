# PMFlavor — open work

### The mixing functional forms

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹` evaluate derived
invariants, but which invariants and how they combine is supplied. This is the main derivation gap
of Paper IV. The structure behind the forms is derived (OVERVIEW, "Where the mixing comes from");
what remains:

* **E8 constructions for the integers the data fix** (`MixingTests`): the `14` of `s₁₂ = π/14`
  (the in-cycle amplitude through the reference's class, `ExchangeAxis`), the `χ` of `|V_ub|`, and
  the `2φ` of the solar angle, where the data require a probability linear in a pentagon cosine
  (`MixingTests.solar_candidates`). The reactor's `3` is constructed (`ReactorConductance`).
* **The `O(1)` coefficients of the node-crossing amplitudes** (`1/χ`, `π + χ`): the node energy
  denominators `e − E` of `NodeElimination`.
* **The size of the parity breaking** that splits `s` from `c` (`ExchangeChirality`): large for
  quarks (`|V_ub|/|V_cb| ≈ 0.09`), small for leptons (`θ₂₃` near maximal; Paper IV's octant
  "running" is this breaking and has no Lean statement).
