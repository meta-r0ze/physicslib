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
  be a through weight (Landauer, as in `PMConstants.HandoffAdmittance`).
* **The `χ` of `|V_ub|`** (`MixingTests.vub_count_unique`). The reactor's `3` is constructed
  (`ReactorConductance`).
* **The `O(1)` coefficients of the node-crossing amplitudes** (`1/χ`, `π + χ`): the node energy
  denominators `e − E` of `NodeElimination`.
* **The size of the parity breaking** that splits `s` from `c` (`ExchangeChirality`): large for
  quarks (`|V_ub|/|V_cb| ≈ 0.09`), small for leptons (`θ₂₃` near maximal; Paper IV's octant
  "running" is this breaking and has no Lean statement).
