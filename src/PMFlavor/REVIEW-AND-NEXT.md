# PMFlavor — open work

### 1. The mixing formulas are ansätze

`s₁₂ = π/(ν−χ)`, `s₁₃ = 1/(χα⁻¹+π)`, `|V_cb| = (π+χ)/(α⁻¹−Dπ)`, `δ_CP = arctan(σ/χ)`,
`sin²θ₁₂ = 1/(2φ)`, `sin²θ₂₃ = (1/χ)(1 + π/(ν+σ))`, `sin²θ₁₃ = (σ−χ)/α⁻¹`. Each evaluates
derived invariants, but the form (which invariants, combined how) is supplied. This is the main
derivation gap of Paper IV.

What the data fix within each form's natural family (`MixingTests`, `ReactorConductance`):
* fixed: `|V_us|` among `π/n` only `n = 14 = ν − χ` (`cabibbo_count_unique`); `|V_ub|` among
  `1/(m Z_geo)` only `m = χ` (`vub_count_unique`, the `π` is a `1%` correction below the error);
  PMNS `sin²θ₁₃` among `n/Z_geo` only `n = σ − χ = 3` (`channel_count_unique`); solar among
  `1/(nφ)` only `n = 2`;
* not fixed at present precision: the `|V_cb|` denominator `Z_geo − nπ` (`n = 2…5`), the
  atmospheric `(1 + π/n)/2` (`n = 15…37`), `δ = arctan(n/2)` (`n = 4…6`).

Constructed so far: the PMNS reactor angle as the node's conductance into the `D − 1` spatial-axis
channels (`ReactorConductance`, Landauer derived in `PMConstants.HandoffAdmittance`). Open: E8
constructions for the other fixed integers (the `14` of the Cabibbo amplitude, the `χ` of `|V_ub|`,
the `2φ` of the solar angle); the unfixed forms cannot be tested until the data sharpen. For the
solar angle the data favour the linear pentagon cosine `cos(2π/5) = 1/(2φ)` over the `E8 → H₄`
norm share `1/(1 + φ²)` (`−2.3σ`) and tribimaximal `1/3` (`+2.4σ`) (`MixingTests.solar_candidates`),
so its construction must give a probability linear in a pentagon cosine.

**Where the mixing comes from (`GenerationLabel`).** Every `E₈` root shifts both walls by the same
glue class, so it conserves the generation label (the omitted class): root dynamics cannot mix
generations, and links built from root moves are diagonal. Mixing needs a single-wall carrier
move, and generations `m`, `m'` mix through the class `m + m'`, a different class for each pair.
Next: the amplitude of a single-wall carrier exchange per class. The reading in `GenerationLabel`
(exchange through the reference's class stays in the reference cell, the other two cross the node)
matches the CKM split, `s₁₂` free of `α` and `|V_cb|`, `s₁₃` of order `α`; the leptons' near-maximal
`θ₂₃` needs its own account.

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
