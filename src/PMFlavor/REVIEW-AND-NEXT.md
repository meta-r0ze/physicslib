# PMFlavor — open work (todo)

Checked mathematics and the downstream handoff are in [`OVERVIEW.md`](OVERVIEW.md).
This file is only what remains. Paper IV builds clean; run `./build.sh PMFlavor` for current counts. Every item below is a physical input no theorem
can supply, a data task, or a genuinely open structural question.

## Open items

#### Phase/cost reading of `δ, ε`

`BreakingPhase` now records `δ = phase mismatch`, `ε = cost`, and
`ExceptionalWall` is the mixing exceptional curve in those variables.
`PhysicalWall = 0<δ ∧ 0<ε<2` and `physicalWall_off_exceptional` proves any
physical wall point lies off the curve.  The numerical `δ, ε` remain wall inputs.

### Flavor as transfer

`TransferFlavor` classifies CKM as boundary conduction, PMNS as capacity
promotion, and the broken link as a coordinate jump.  The mixing overlap is the
transfer-amplitude ledger (`mixingOverlapAmplitude_eq_rootM`), and the E8 capacity
ratio is `pmnsCapacity/ckmCapacity = 21/16`, with transfer impedance `16/21`.
`normalizedOverlap` turns a complex overlap into a unit-modulus entry, and
`FlavorSector`/`normalizedSectorEntry` label CKM and PMNS entries.  The impedance
is the capacity ratio `16/21`; `wallImpedance` and `transferImpedance_eq_wall`
give the conditional wall-dispersion identification.  The capacity fractions are
`16/37` (CKM) and `21/37` (PMNS), so the PMNS basin is the larger one.  Deriving
the wall masses remains open.  Numerical transfer parameters remain wall inputs.

### 1. Numerical link weights (physics, not a proof)
`BreakingLink.brokenLink δ` and `brokenLinkB ε` are structural: the doublet splits
for any `δ ≠ 0`, the `Z₂` obstruction is removed for any `ε ≠ 0`. The **values** of
`δ, ε` are dynamical wall couplings and cannot be derived from the persistence
axioms. Do not fit them by hand (that is numerology); a substrate determination is
the only valid route.

### 2. Full all-nonzero mixing (structural part closed; one physical check remains)
`MixingMatrix.all_nonzero_mixing_interval` proves every entry of the mixing overlap
is nonzero on the **whole square `0 < δ, ε ≤ 4`** (via `rootP > 4`, `1 < rootM`,
`rootM < 5/2`), and `all_nonzero_mixing_witness` gives the `δ = ε = 2` point. The
global statement is false: `MixingMatrix.ip_M_M_vanishes_at` proves the term
`rootM+rootM−5` vanishes at `δ = ε = 9/2` (`rootM 9/2 = 5/2`).

The structural gap is now closed by `MixingMatrix.all_nonzero_mixing_global`:
for all positive `δ, ε`, every entry is nonzero **unless** the pair lies on the
explicit curve `δ = rootMInv (5 − rootM ε)`. `rootM_sum_eq_five_imp` shows any
zero of the `rootM/rootM` overlap must lie on that curve, so for fixed `ε` there is
at most one exceptional `δ`; the exceptional set is a graph, not a region. For
`ε > 2` this is an iff (`rootM_sum_eq_five_iff_of_two_lt`); for `ε ≤ 2` the sum is
automatically below `5` (`rootM_sum_lt_five_of_le_two`), so there are no zeros
there. Remaining: once item 1 fixes the physical `(δ, ε)`, check that point is off
the curve. No further structural proof is needed.

### 3. Derive φ (open, no known route)
`FlavourPulls.φ = (1+√5)/2` is a postulate; the solar angle `1/(2φ)` and its octant
(`WolfensteinOctant.solar_lt_half_iff`) reduce to `1 < φ < 2`. Either derive the
golden ratio from the substrate, or state explicitly that the solar sector is a
one-parameter postulate. No Lean path from E8/clock data to φ is known.

### 4. Physical preparation and the energy-spread bound (physics)

`FlavourCoherence` states the chord-branch bound as phase coherence:
`phaseDrift e t ≤ π`, `PreparationSpreadBound`, `oneTickCoherent`, and
`perStepRestores` for exact `2π` restoration.  The physical preparation spread
is an explicit input, not a claimed theorem.  `rawSpectrum_not_preparation` proves
the raw link eigenvalues cannot satisfy it; the physical energies must come from
the wall dispersion.
`ChordBranch` reduces the branch condition to `t ≤ tStar` and to the *energy*
spread `≤ π/43`; `MixingMatrix.spread_exceeds_pi_over_43` shows link eigenvalues are
the wrong scale. Remaining: a concrete preparation protocol (not just
`LightFlavourPreparation`'s existence theorem) and a proof that the physical energy
spread is within `π/43`, which needs the momentum/detuning of the physical state.

### 5. Per-step maintenance contract (structural, hard)
`LeptonAxisRestriction` proves the per-cycle (three-step) contract. A per-step
(one-step) contract needs exact within-step state restoration; the gap is documented
there. This is the hardest remaining structural proof.

### 6. Carrier-current identification (cross-paper, partly done)
`WeakCurrentBridge` proves the native current's chiral projector **is** Paper II's
weak V−A projector: `spinProjector_eq_PL` (`spinProjector = WeakVertex.PL`), with
`spinProjector_idempotent` / `_hermitian` / `_trace` transported from PM-2, plus
`vertex_eq_native` and `modelCurrent_eq_PL`. So the chirality is not a free choice
*inside Paper II's supplied four-component representation*; `PMAction.ConcreteFermion`
is explicit that the representation does not derive gauge content.
Remaining (physical inputs): the flavour generator `G`, the carrier charge values,
the mediator/statistics, and the chiral representation itself. Paper II gained the su(2) doublet algebra
(`ChargedCurrent.T3`, `commutator_T1_T2`, `commutator_T3_Tp/Tm`, `commutator_Tp_Tm`,
`anticommutator_Tp_Tm`) and `WeakVertex.PL_*` for selection-rule use.

### 7. Data module (data work, outside the axiom-checked tree)
`FalsifiablePredictions.prediction_ledger` is the auditable input. A separate module
must record measurements with provenance, uncertainties and covariance and evaluate
residuals against the ledger. Do not put measured numbers into the theorem tree.

## Suggested order

1. **Item 2** — structural part closed; after item 1 fixes `(δ, ε)`, check the
   physical point is off the explicit exceptional curve.
2. **Item 5** — deepest structural proof; needs exact within-step restoration.
3. **Item 4** — concrete preparation protocol and the physical `π/43` bound.
4. **Item 6** — chirality is forced on the zero kernel by `PM-2`; the remaining part
   is the physical generator/charge/mediator/representation input and the off-kernel
   extension.
5. **Item 3** — no derivation route exists; keep the solar sector a postulate until
   one is found.
6. **Items 1 & 7** — physical/data tasks, done last and kept out of the tree.

## Lean-review audit flags

These are provenance/scope findings from `tools/lean_review.tex`, not missing Lean
proofs. They are separate from the open physics items above.

* **Hypercharge is constrained upstream up to labeling.** PMConstants
  `ReferenceLink.standard_or_conjugate` derives either the standard charges
  (ν neutral) or their conjugate (e neutral) from flux conservation, one unit link
  and `|Y_L| = 1`; the sign is an `e`/`ν` convention, not a physical choice.
  PMFlavor uses the ν-neutral branch. Remaining: the representation/flux content and
  the unit-link premise.
* **V−A chirality is forced on the zero kernel, not globally.** PMAction
  `ChiralityConvention.projector_unique_on_kernel` shows any operator that kills the
  unphysical first-wall background and fixes the exchanged physical reference
  agrees with the chiral projector on the zero kernel; `projector_eq_fromBlocks_PL`
  identifies that projector with block-diagonal `P_L`. Still inputs: attaching the
  weak gauge representation and extending the identification off the kernel.
* **Cabibbo deficit is upstream; the CKM application is not.** PMConstants
  `FlavourDressing.cabibbo_deficit_per_direction` proves `1 − (1−η)/D = 687/688`
  from the reference-frame overhead; `CabibboDressing.q2_eq_per_direction_reference`
  connects `CKMDressing.q2` to it. Remaining: the claim that the CKM first row
  inherits the reference deficit.
* **Flavour formulas are ansätze.** `FlavourInvariants` proves the numerals
  downstream equal the supplied formulas evaluated on derived `ν, σ, χ, D`; it does
  not derive the six functional forms.
  `formula_definitions_use_no_measurement_literal` is a definitional `rfl`
  restatement, not evidence of derivation.
* **Measurement pulls are a leaf.** The PDG/NuFIT pulls and the first-row benchmark
  live in `FlavourPulls`; the LHCb/PDG benchmark pulls now live in
  `ExperimentalPulls`. Derivation modules import `FlavourPostulates`, not either
  comparison leaf.

## Verification

Run `./build.sh PMFlavor` for this library. The top-level `./build.sh audit` checks
the whole tree, not just PMFlavor. No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.

### Protected-state overlap is δ-independent

The state `anti` is an eigenvector of `brokenLink δ` for every `δ`, so the
protected-state overlap with the `Z₂`-breaking sector depends only on `ε`.
The absolute wall scale `δ` cancels in this observable; only the breaking cost
`ε` matters.  Full mixing entries do depend on `δ`
(`fullMixing_delta_dependence`), so `δ` is physical for the full CKM/PMNS
entries and needs one anchor.  The unit-toll anchor `unitWall = (1,1)` is
physical, off the exceptional curve, and gives all-nonzero full mixing
(`unitWall_all_nonzero`).  It is an anchor choice, not an E8 derivation.

### Unit-toll wall mixing test

At `unitWall = (1,1)`, the normalized protected-state mixing entries are:

| row \ col | antiB | P | M |
|---|---:|---:|---:|
| P | 0.1464 | 0.9571 | 0.25 |
| M | −0.8536 | 0.25 | −0.4571 |
| anti | 0.5 | 0.1464 | −0.8536 |

This is a **large-mixing** matrix, PMNS-like rather than CKM-like.  So the
unit-toll anchor is a plausible neutrino-sector anchor, but not a CKM anchor.
The CKM sector needs a different scale/mode anchor.
