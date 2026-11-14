# PMFlavor — open work

### 1. The mixing formulas are ansätze

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹`. Each evaluates
derived invariants, but the form (which invariants, combined how) is supplied. This is the main
derivation gap of Paper IV.

### 2. The `687/688` first-row dressing

`PMConstants.FlavourDressing` identifies `1/688` as the per-direction reference deficit
`(1−η)/D`; the claim that the CKM first row inherits it is the model step. Against the first-row
sum `0.9984 ± 0.0007` the whole-frame share `1/172` and one row's `1/43` are excluded, but the
share over all `D` directions (`1/688`) and over the `D − 1` spatial ones (`1/516`) both fit
within `1σ` (`CabibboDressing.frame_share_excluded`, `direction_shares_fit`), so the data do not
fix the divisor. Open with it: the three or more channels that must carry the lost probability
(`CKMDressing.dilation_needs_three`), and the `>2%` Jarlskog disagreement with Paper III once
dressed (`papers_disagree_dressed`).

### 3. The V−A projector off the kernel

`PMAction.ChiralityConvention.projector_unique_on_kernel` forces the projector on the zero
kernel. Attaching weak to one wall is derived: the weak refresh is the sign exchange of the whole
sector that holds the reference (`PMConstants.WeakUniform.refresh_uniform`, uniform from the D₄
roots and commutation with colour) and acts on that sector only (`CarrierActions.weak_chiral`),
with the tag read as the wall. Off the kernel, the light band's effective Hamiltonian (projected
on the zero modes) commutes with the wall chirality, and on it `(1 − Γ)/2` is exactly the second
wall's block (`PMAction.ChiralLightBand.light_conserves_chirality`, `projector_on_light_band`):
the identification holds through first order in `k`. Open: the `O(k²/gap)` wall mixing through
the gapped modes, if a constant needs it.

### 4. Inputs that are not derivable

* **Wall anchor magnitude `δ` (and `ε`).** `BreakingPhase` records `(δ, ε)`; the direction
  (lepton axis) and functional form are E8 (`MixingMatrix.rootP/rootM_eq_substrate`), the
  magnitude has no cost functional. Anchors: `TransferFlavor.unitWall`, `ckmWall` (`χ/ν`).
* **Absolute wall-mass scale.** The ratios are E8 (`WallMassRatio.capacity_ratio_sq`,
  `coupling_ratio`); the absolute scale is the usual external unit, like `m_e`.
* **Octant running.** Paper IV's "running resolves the octant anomaly" has no Lean statement.


- Identify the physical interaction that realizes the reference-stabilizer mediator.
- The entries of the inter-wall link used by the generation model in PMConstants depend on the flavour dynamics.
