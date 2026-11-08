# PMFlavor — overview of checked results

*Persistence Mechanics of the Quantum Vacuum IV: Information Transfer.*

This is the single overview of what Paper IV proves and how it hands off to
Papers V–VI. The actionable open work is in [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md);
build/layout instructions are in [`README.md`](README.md). The Lean source is the
ground truth; theorem names below are entry points, not an exhaustive list.

## Scope

Paper IV builds on the Paper I substrate (E8, clock Δ = 43, invariants
D = 4, ν = 16, σ = 5, χ = 2) and Paper II/III wall and register results. It treats
the flavour sector — CKM/PMNS mixing, wall spectra, propagation, reference
persistence, and a transfer/work cost — as a constrained-persistence application.
Nothing here compares to measurement; the falsifiable claims are collected in one
ledger. No Paper V–VI imports are allowed.

## Current geometric status

The flavour angles are now geometry-first, not operator-fit-first.

* CKM: `FlavourInvariants` restates the Paper IV formulae in derived invariants:
  `s12 = π/(ν−χ)`, `s13 = 1/(χ α⁻¹+π)`, `|Vcb| = (π+χ)/(α⁻¹−Dπ)`,
  `δCP = arctan(σ/χ)`.
* PMNS: `PMNSGeometry` formalizes the bulk-strain angle
  `sin²θ23 = (1/χ)(1+π/(ν+σ))`, the colour-remainder angle
  `sin²θ13 = (σ−χ)/α⁻¹`, and the explicit upper-octant / `sin δ<0` branches.
* Solar: `GoldenGeometry` derives `φ` from pentagon Ptolemy; `SixHundredCell`
  gives an explicit 600-cell pentagon with edge `1/φ`, diagonal `1`, ratio `φ`;
  hence `sin²θ12 = 1/(2φ)`.
* `α⁻¹` is imported from `PMSubstrate.geometricIndex`; it is substrate, not flavour.
* Path/cycle operators were exploratory candidates.  They are not the primary
  derivation and no longer have separate documents.

## What is checked

**Matrices and mixing.** `CKM`, `PMNS`: complete complex matrices with exact
unitarity, determinant 1, the Jarlskog quartet, and certified squared-entry /
Jarlskog intervals (`PMNSIntervals`: `−0.0217 < J < −0.0215`). The PMNS phase is
fixed by the persistence sum rule `|U_μ2| = |U_τ2|` (`ReferenceFlavour`), on the
`sin δ < 0` branch. Unitarity triangles have area `|J|/2`
(`UnitarityTriangle.area_is_half_J`), with `68.16° < γ < 68.17°`.

**Wall spectrum and native carriers.** `WallSpectrumLink` identifies branch
energies with the relativistic energy law and the light/heavy seesaw;
`FlavourWallReduction` gives the exact multi-flavour reduction; `NativeFlavour*`,
`NativeMassBasis`, `LightFlavourPreparation` realise prepared eigenmodes on the
native carrier and reproduce exact flavour evolution and probabilities.

**Reference persistence.** `ReferenceSpectrum`: persistence iff a single-energy
eigenspace. `SpectralVariance`, `FlavourStationarity`: residual coordinates and
gap bounds. `persistent_single_frequency`: a persisting state is one energy/
frequency, hence on-shell (used by Paper V).

**Selection and restoration.** `AllRootRestoration`, `RootRepairSelection`,
`RestorationBudget`: the six-reflection restoring alphabet, unique cheapest word,
minimum density. The five selection tests (`ReferenceSelection`,
`NativeReferenceFreedom`, `FlavourResponseSelection`, `SelectionSymmetry`,
`TransitionSelection`) isolate what a persistence cost can and cannot select.

**Lepton axis, Dirac survival.** `LeptonAxisRestriction` (per-cycle contract) plus
`MassTermLaw` give `dirac_survival`: only the Dirac neutrino mass term survives;
active-Majorana and sterile terms are unreachable.

**Transfer cost and generation selection.** `RelativeFrameCost` prices a frame by
`‖AB−BA‖²/12 = Σ gap·weight/12`. `TransferWorkLaw` shows the least-work route is
the smallest-gap pair; `SpectralGapOrder` derives the gap ordering from the
spectrum (`gap = 2 − 2cos|t·Δe|`); `ChordBranch` reduces the one-branch hypothesis
to `t ≤ tStar` and discharges it at `tStar`; `TransferAmount` shows any positive
transfer costs positive work.

**The link, derived.** `SubstrateLink.linkOverlap` is the glue-class overlap
matrix (`2` diagonal, `1` off), `S₃`-invariant with spectrum `{4,1,1}` — a
degenerate light doublet. `BreakingLink.brokenLink δ` (lepton-axis weight on
generation 0) splits it for any `δ ≠ 0`; `brokenLinkB ε` breaks the residual μ–τ
`Z₂` and loses the protected antisymmetric state. `MixingMatrix` computes the
protected-state overlap and shows the shared-state no-go is resolved
(`anti_overlaps_all`), all-nonzero mixing on the physical square `0 < δ, ε ≤ 4`
(`all_nonzero_mixing_interval`), a global version whose zero set is exactly the
explicit curve `δ = rootMInv (5 − rootM ε)` for `ε > 2` and empty for `ε ≤ 2`
(`all_nonzero_mixing_global`, `rootM_sum_eq_five_iff_of_two_lt`), and a witness
point (`all_nonzero_mixing_witness`).

**Derived inputs and Wolfenstein.** `FlavourInvariants` shows the numerals in the
six supplied flavour formulas are the Paper I invariants evaluated; the functional
forms themselves are ansätze, not E8 theorems. Upstream
`PMConstants.FlavourDressing` identifies `687/688` as the per-direction reference
deficit `1 − (1−η)/D`; `CabibboDressing` connects it to `1 − 1/(νΔ)`. The remaining
model step is the claim that the CKM first row inherits that deficit. `Wolfenstein` defines
λ, A, ρ̄, η̄ on the paper's own matrix and proves `η̄ > ρ̄` (from `σ > 2χ`) and the
`O(λ³)` truncation structure. `WolfensteinOctant` proves the solar/atmospheric/
reactor octants, and that the solar octant is exactly `1 < φ < 2`.

**Current chirality tied to Paper II.** `WeakCurrentBridge.spinProjector_eq_PL`: the
native flavour current's chiral projector is Paper II's `P_L` **within Paper II's
chosen four-component representation**. PMAction
`ChiralityConvention.projector_unique_on_kernel` now forces that projector on the
zero kernel from the reference conditions, and
`projector_eq_fromBlocks_PL` matches it to block-diagonal `P_L`. The remaining input
is attaching the weak gauge representation and extending the projector off the
kernel. The projector is rank two, so `modelCurrent G = P_L ⊗ G` is inherited within
that representation, not chosen separately.

**CP for the next papers.** `Downstream`: `pmJ > 0` (CKM CP violated, positive
Jarlskog → baryon-asymmetry sign), `cp_conserved_iff` (`pmJ = 0 ↔ sin δ = 0`), and
the leptonic side `PMNS.jarlskog_nonpos` (opposite sign to CKM).

**Falsifiable ledger.** `FalsifiablePredictions.prediction_ledger` bundles every
measured-input-free claim, conditional on the model inputs above, in one conjunction — the auditable input
to a data fit (the fit itself is data work, outside the axiom-checked tree).

## What is *not* derived

`φ = (1+√5)/2` is now derived from pentagon Ptolemy and the explicit 600-cell
pentagon (`GoldenGeometry`, `SixHundredCell`). The six mixing functional forms are
still supplied geometric ansätze; `FlavourInvariants` only removes the literal-numeral
duplication. The `687/688` Cabibbo dressing is re-expressed, not
derived. The numerical breaking weights `δ, ε` are dynamical, not fixed. Link
eigenvalues are not the physical energy scale, so the `π/43` chord bound is about
energies. The V−A projector is forced on the zero kernel by reference persistence
(PM-2 `ChiralityConvention.projector_unique_on_kernel`); attaching the gauge
representation and extending it off the kernel remain inputs. The neutrino
Dirac-survival result is conditional on the upstream
flux/one-link hypercharge representation; the `Y_L` sign is an `e`/`ν` convention
(`ReferenceLink.standard_or_conjugate`), not a physical choice. Measured PDG/NuFIT
comparisons live in the `FlavourPulls` and `ExperimentalPulls` leaves and are not
imported by the CKM/PMNS derivation modules; no measured number enters the
derivation closure.

## Downstream handoff

`PM-5-Decay` and `PM-6-Cosmo` both build against this tree. Paper IV supplies
them the CP input (`Downstream`), external-state on-shellness
(`persistent_single_frequency`), unitarity/mixing (`PMNS`, `CKM`), and Jarlskog
bounds. Their remaining work is their own physical modelling (interaction,
phase-space measure, decay-law cost for V; background/perturbation/baryon dynamics
for VI) — not missing Paper IV proofs.

## Verification

Run `./build.sh PMFlavor` for this library. The top-level `./build.sh audit` checks
the whole tree, not just PMFlavor. No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
