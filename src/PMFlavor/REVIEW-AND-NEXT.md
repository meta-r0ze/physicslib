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
`ExchangeAxis` derives which pair mixes in-cycle: `6` of the `8` vector-class displacements avoid
the reference axis, while every spinor and conjugate-spinor displacement touches it, so by
`LeptonAxisRestriction` only the pair mixing through the reference's class `v` has gauge-repairable
exchange; the other two pairs must pass the reference node. This matches the CKM split (`s₁₂` free
of `α`; `|V_cb|`, `s₁₃` of order `α`). `ExchangeChirality` places
the `s`/`c` split: in the reference-free generation the two spinor classes sit on opposite walls,
and the class swap is a symmetry of the wall incidence only together with the wall exchange, the
parity that flips chirality. So `|V_ub| ≠ |V_cb|` is the charged current's parity violation, in
leptons as well (consistent with `GenerationBreaking.pmns_no_shared_state`). The price of a node
passage is the derived through weight `α` (`PMConstants.HandoffAdmittance`), but `NodePassage` shows
the quark node-crossing mixings cannot be passage probabilities with whole channels (`|V_cb|²`,
`|V_ub|² < α`, and `|V_ub|² < α²`): they enter as link amplitudes linear in `α`, while for the
reactor angle the data allow both the conductance `3α` and an amplitude `20α` or `21α`. `NodeElimination`
accounts for that split: with no in-cycle exchange the node-crossing coupling is the Schur
complement `t₁t₂/(e − E)`, two legs of through weight `α` each, so an amplitude `∝ α` for states
reaching the node from off the reference axis (quarks) and one leg, a probability `∝ α`, for states
on the reference's own axis (leptons). Open: the energy denominators that set the `O(1)`
coefficients (`1/χ`, `π + χ`), the in-cycle amplitude through `v` (the `14` of `s₁₂`), and the size of the parity breaking
in each sector (large for quarks, `|V_ub|/|V_cb| ≈ 0.09`; small for leptons,
`θ₂₃` near maximal).

### 2. The first-row dressing: inheritance

The dressing is now `q² = 515/516`: the minimal dilation has exactly three outlet channels
(`DressingChannels`), and a registered loss puts no weight on the time axis, so the reference
deficit `1 − η` is shared over the `D − 1` spatial outlets (`DressingEvent`, the event principle of
`PMConstants.VevEvent`). The earlier `687/688` was the four-axis share. First-row sum
`1 − 1/516` is `0.5σ` from `0.9984 ± 0.0007`. `DressingInheritance` derives
why the quark rows carry it and muon decay does not (so it does not cancel against `G_F`): the
reference's maintenance moves along its own axis, the time axis is the maintenance direction, so the
lepton axis is time and colour transitions are spatial; only spatial transitions register a loss.
Premise: carrier vectors and lattice hop directions share the `D₄` coordinates. Open: a test beyond
the first row (each CKM row and column `1/516`, PMNS unitary, hadronic/leptonic `W` ratio `q²`).

### 3. Inputs that are not derivable

* **Wall anchor magnitude `δ` (and `ε`).** `BreakingPhase` records `(δ, ε)`; the direction
  (lepton axis) and functional form are E8 (`MixingMatrix.rootP/rootM_eq_substrate`), the
  magnitude has no cost functional. Anchors: `TransferFlavor.unitWall`, `ckmWall` (`χ/ν`).
* **Absolute wall-mass scale.** The ratios are E8 (`WallMassRatio.capacity_ratio_sq`,
  `coupling_ratio`); the absolute scale is the usual external unit, like `m_e`.
* **Octant running.** Paper IV's "running resolves the octant anomaly" has no Lean statement.
  `ExchangeChirality` now places the deviation of `θ₂₃` from maximal: it is the `s ↔ c` breaking,
  which only the charged current's parity violation supplies; its size is not derived.


- Identify the physical interaction that realizes the reference-stabilizer mediator.
- The entries of the inter-wall link `Y` (`PMConstants.GenerationWalls`): the structure is now
  fixed (`GenerationLabel`, `ExchangeAxis`, `ExchangeChirality`, `NodeElimination`): root moves are
  diagonal, one pair mixes in-cycle through the reference's class, the other two through the node
  as two-leg amplitudes `∝ α` (one leg for lepton-axis states), split by parity. The magnitudes
  (node energy denominators, the in-cycle amplitude, the parity-breaking size) are open; see item 1.
