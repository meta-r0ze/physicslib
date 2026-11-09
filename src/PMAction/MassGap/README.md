# PMAction/MassGap — the mass gap of the distinction substrate

PM's substrate is a field of distinctions: binary site states whose cost is the number of cut
edges (`PMSubstrate.Distinctions.only_distinctions_cost`), with a change between ticks costing
one distinction too (`SpacetimeCost`). This folder proves that substrate has a volume-uniform
mass gap. Lean source is the ground truth; this file is a map.

**What this is not.** In PM the gauge field is a different object: continuous unitary links,
generated coherently by the E8 root-response operators under smooth controls
(`Machine/NativePacketUpdate`). Discrete root permutations cannot supply it
(`NativePacketRouting.pure_permutation_refinement_trivial`). The Wilson action is not derived as a
survival cost (`LatticeGibbs`), and the gauge group and `β` are not selected (`D4Gauge`,
`LinkConsistency`). So the gap of the gauge layer is the general quantum Yang–Mills problem, which
is out of scope (`AGENTS.md`; `OPEN-PROBLEMS.md` P4). The gauge layer's classical continuum
limit and finite-volume Euclidean setup live in `PMAction` proper (`LatticeGibbs`,
`ReciprocalReflection`, `OsterwalderSchrader`, `LatticeSiteAction`, …).

## Start here

**Theorem** (`SlabGap.slab_gap_explicit`). Let `G` be a finite connected graph (space), with
plaquettes that generate its cycle space, of size `≤ k`, at most `m` through any edge, and `G` of
degree `≤ Δ`. Put `D = max(k,4)·(m + 8Δ)`. Let `T` be the PM transfer matrix of the slab
`G □ [0, L]`: every boundary edge, spatial or temporal, costs one distinction, with weight
`q = e^{−β}`. If `√q ≤ 1/(16 (D+1)²)`, then on flip-even states the top eigenvalue `Λ` of `T²` is
simple, and every other eigenvalue is `≤ q·Λ`. The bound is uniform in `|G|` and `L`.

The chain, one file per step:

1. History sum = contour polymer gas: `ContourGas.contour_gas_eq`, `HistorySum.history_sum`
   (slab cycle space: `SlabGeometry.slab_generate`).
2. Slab sum = transfer product: `TransferSlab.slab_transfer`.
3. Even parity observables = sign twists of the gas: `SlabObservables.corr_eq_Z`.
4. Euclidean clustering at rate `μ` per tick: `SlabClustering.slab_clustering`, via the
   supersolution influence bound `PolymerInfluence.influence` and the Dobrushin criterion.
5. Spectral assembly: `SpectralBounds.visible_top`, `Walsh`, `GapFromCorrelation`, giving
   `SlabGap.slab_gap`.
6. The regime is not empty, and the degree bound is proved: `SlabGap.regime_numerics`
   (`μ = √q`), `SlabDegree.slab_degree_le`.

Concrete form (`CubicBox.box_mass_gap`): space is the `d`-dimensional box of any side, so spacetime
is `(d+1)`-dimensional (`d = 3` gives Euclidean 4D). With `q = e^{−β}`, if
`β ≥ 2 log(16 (32d² + 64d + 1)²)` (`≈ 30.2` for `d = 3`), every flip-even excited state has mass
`≥ β/2` per tick, uniformly in the box size (`SlabGap.slab_mass_gap`: gap = coupling, as in
`DefectGap.gap_eq_coupling`). The constant is crude, not optimized.

Check it: `lake build PMAction.MassGap`, then
`#print axioms PMAction.MassGap.SlabGap.slab_gap_explicit` (expected: `propext`,
`Classical.choice`, `Quot.sound`).

Not claimed: the flip-odd sector (tunnelling between the two vacua; no volume-uniform gap is
expected there), continuous link groups (`PeierlsDichotomy`: `U(1)` has no Peierls condition), or
the continuum `SU(N)` (Clay) problem.

## Reading order

| Module | What it proves |
| --- | --- |
| `GapStability` | Quadratic-form gap of a diagonal energy survives a perturbation with `ε < m/2`. |
| `DefectGap` | PM's distinction cost (one transition per boundary edge): unique vacuum, every excitation `≥ 1`, volume-uniform; survival weight = Gibbs weight `e^{−β·cost}`; local defects cost locally. |
| `HessianGap` | Gauge-covariant kinetic form `Σ‖a(head) − U a(tail)‖²` has gap `≥ 1/(L·K)` on regions that reach the vacuum along short paths, for any unitary links (diamagnetic + canonical-path Poincaré); `1/Δ²` on a causal line; `no_gap_without_vacuum`. |
| `ContourCount` | Rooted animals ≤ `D^{2(k−1)}` (spanning walks); polymer sum and Kotecký–Preiss smallness, volume-independent. |
| `PolymerConvergence` | Polymer partition function, deletion recursion, **Dobrushin's criterion** (positivity, ratio bounds `1 ± x`), extensive bounds, Weierstrass inequality. |
| `PolymerDecay` | **Decay of influence**: weighted recursion; ratios differ by `≤ 2 x_γ b_γ θ^k` when allowed sets agree to depth `k`. |
| `PolymerBridge` | Dobrushin and decay hypotheses from per-site sums; per-site sums from `ContourCount`; animal re-rooting. |
| `GapFromDecay` | Euclidean decay `⟨v, Tᵗ v⟩ ≤ C λᵗ` caps every excited eigenvalue at `λ`. |
| `PeierlsDichotomy` | Finite link values satisfy the Peierls condition; `U(1)` does not (no gap for the photon from this route). |
| `SpacetimeCost` | **PM premise**: a site changing between ticks is a distinction. Spacetime gap, unique vacuum, one activity `q = e^{−β}` for every boundary edge. |
| `ContourRepresentation` | Cohomology core: cuts are exactly the edge sets every closed walk meets evenly; the vacuum-rooted history is unique; plaquette-closed pieces of a cut are cuts (premise: plaquettes generate the cycle space). |
| `ContourGas` | **Exact identity**: PM's history sum `Σ q^cost` equals the polymer partition function of plaquette-connected contours with activity `q^|γ|`. |
| `PolymerCorrelation` | Decay of correlations (depth form): the cross-ratio of two far-apart allowed-set modifications is within `Π(1+δ_a) − 1` of `1`. |
| `PolymerInfluence` | **Influence form** (no depth assumption): for any supersolution `f` of `f γ ≥ x_γ Σ_{r~γ} stepBound r`, ratios in sets differing only on `E` differ by `≤ f γ`; toggle closeness; `cross_ratio_of_close`. Needed because contours touch arbitrarily large contours. |
| `GapFromCorrelation` | Truncated two-point decay `≤ C ρᴸ Z_L²` of an eigenvector caps its eigenvalue at `ρ Λ` (`gap_of_truncated_decay`). |
| `GapChain` | Assembly: `contour_decay` (explicit, volume-uniform, `θ = 4Kq/(1−2q) ≤ 8Kq`) and the conditional gap `gap_of_euclidean_decay`. |
| `HistorySum` | Weighted contour gas identity; `cutSet` of a configuration; `history_sum`: sums over vacuum-rooted configurations are sums over even edge sets. |
| `SlabGeometry` | The open-time slab `G □ [0,L]`, unit squares and spatial plaquettes; `slab_generate` (plaquettes generate the slab's cycle space). |
| `ParitySigns` | Spins as products over boundary edges (`spin_eq_cut`, `parity_eq_cut`, `observable_weight`). |
| `SlabTime` | Tick of an edge (`tau`); a contour spans at most `|γ| − 1` ticks. |
| `TwinGas` | Sign twins: a signed gas as a toggled allowed set of an unsigned twin gas. |
| `SlabClustering` | **Euclidean clustering** on the slab: `|Z_AB Z_0 − Z_A Z_B| ≤ C e^C μᴸ Z_A Z_B` via a time-decaying supersolution (`twin_super`). |
| `TransferHistory` | `⟨u, Tᴸ w⟩` is a sum over histories; the PM weight `r^c q^ham r^c` (`r² = q`) multiplies to `q^cost`. |
| `TransferSlab` | `cut_decomp` (boundary = spatial cuts per slice + flips per tick); **`slab_transfer`**: the slab sum is `⟨v₀f, Tᴸ v₀g⟩`. |
| `SlabObservables` | Even slice observables are sign twists (`slice_obs`); `corr_eq_Z`; **`transfer_clustering`** with an `L`-independent constant. |
| `Walsh` | Walsh expansion; flip-even functions have only even characters. |
| `SpectralBounds` | Spectral sum; **visible top** `κΛᴸ ≤ ⟨v, (T²)ᴸ v⟩ ≤ KΛᴸ`; `rate_le`. |
| `SlabDegree` | Plaquette-graph degree of the slab `≤ max(k,4)·(m+8Δ)`, independent of `L`. |
| `CubicBox` | `d`-dimensional boxes built by iterating the slab step; explicit bounds (`k ≤ 4`, `m ≤ 8d²`, `Δ = 2d`); **`box_mass_gap`**. |
| `SlabGap` | **The gap**: in the flip-even sector of `T²`, every eigenvalue is `≤ μ²Λ` or equals the top `Λ` (eigenvector seen by `v₀`); the even top is simple. Uniform in volume and slab length. |

## Status

Proved, no `sorry`: everything above. The chain closes in `SlabGap.slab_gap_explicit` (see Start here); the general form is `SlabGap.slab_gap`: for the PM transfer
matrix `T` on a slab, in the low-cost regime (`SlabGap.Regime`: the `slab_clustering` conditions
on `q`, `μ < 1`, `D`), the flip-even spectrum of `T²` has a simple visible top `Λ > 0` and every
other even eigenvalue is `≤ μ² Λ`, with `μ` fixed by `q` and `D` alone.

Premises and scope:
- The PM premise is `SpacetimeCost`: a site changing between ticks is a distinction and costs
  the same as a spatial one.
- The coupling is not fixed by PM: the survival `p = e^{−β}` per transition is free
  (`PMSubstrate.Vacuum.survival_geometric`). The theorem holds for every `β` above the threshold.
- The gap is for the flip-even sector. The odd sector (tunnelling between the two vacua) has no
  volume-uniform gap and is not claimed.
- The gauge layer is not covered (see the top of this file). `PeierlsDichotomy` also shows this
  contour route cannot reach continuous link groups.

**This branch is closed.** It reopens only on a new premise: PM deriving `β`, or identifying the
gauge Wilson cost with the distinction/survival cost.
