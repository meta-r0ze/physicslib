# PMFlavor — open work

### 1. The mixing formulas are ansätze

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹`. Each evaluates
derived invariants, but the form (which invariants, combined how) is supplied. This is the main
derivation gap of Paper IV.

### 2. The `687/688` first-row dressing

`PMConstants.FlavourDressing` identifies `1/688` as the per-direction reference deficit
`(1−η)/D`; the claim that the CKM first row inherits it is the model step.

### 3. The V−A projector off the kernel

`PMAction.ChiralityConvention.projector_unique_on_kernel` forces the projector on the zero
kernel. Attaching weak to one wall is derived: the weak refresh is the sign exchange of the whole
sector that holds the reference (`PMConstants.WeakUniform.refresh_uniform`, uniform from the D₄
roots and commutation with colour) and acts on that sector only (`CarrierActions.weak_chiral`),
with the tag read as the wall. Open: extending the projector off the kernel.

### 4. Inputs that are not derivable

* **Wall anchor magnitude `δ` (and `ε`).** `BreakingPhase` records `(δ, ε)`; the direction
  (lepton axis) and functional form are E8 (`MixingMatrix.rootP/rootM_eq_substrate`), the
  magnitude has no cost functional. Anchors: `TransferFlavor.unitWall`, `ckmWall` (`χ/ν`).
* **Absolute wall-mass scale.** The ratios are E8 (`WallMassRatio.capacity_ratio_sq`,
  `coupling_ratio`); the absolute scale is the usual external unit, like `m_e`.
* **Octant running.** Paper IV's "running resolves the octant anomaly" has no Lean statement.


- Identify the physical interaction that realizes the reference-stabilizer mediator.
- The entries of the inter-wall link used by the generation model in PMConstants depend on the flavour dynamics.
