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
is out of scope (`AGENTS.md`; `OPEN-PROBLEMS.md` §4). The gauge layer's classical continuum
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

**This branch is closed.** See *The goal of this branch, and where it stops* below.

## The Clay problem, and why this branch does not claim it

The Millennium problem (Jaffe–Witten) asks for two things: for **every compact simple gauge
group**, construct a non-trivial quantum Yang–Mills theory **on ℝ⁴** satisfying axioms at least
as strong as Wightman / Osterwalder–Schrader, and prove it has a mass gap `Δ > 0`. The prize
also requires refereed publication and general acceptance after two years. Lattice gaps,
including numerical lattice evidence, do not count: the object is the continuum theory.

This branch cannot reach that, for structural reasons rather than lack of effort:

1. **PM answers a different question.** PM's substrate is discrete, and the continuum is a
   readout. A lattice construction could reach the continuum target if its interacting gauge
   correlations had a controlled, nontrivial limit as the spacing tends to zero. PM currently
   establishes a classical action limit and a separate gap for its distinction substrate.
2. **The missing piece is not in PM.** The unsolved part is control across scales as the lattice
   spacing goes to zero (a renormalization group for 4D non-Abelian theory). Nothing in the tree
   addresses it.
3. **PM's own coupling sits outside every provable regime.** `PMConstants.EventStiffness`
   fixes the colour coupling at `g₃² = 4πα·N_sys/(12η) ≈ 1.48` (`StrongLedgerBounds`), that is
   Wilson `β ≈ 4` for SU(3), up to PM's normalization factor of order one. Strong-coupling and
   curvature (Lichnerowicz-type) gap arguments need `β ≪ 1`; weak coupling is the Clay problem
   itself. At `β ≈ 4` lattice SU(3) is numerically confining, consistent with a gap, but no known
   argument proves one there.

## The goal of this branch, and where it stops

**Goal.** A self-contained, formally verified claim that an outside expert can check without
accepting PM: a volume-uniform mass gap for the ℤ/2 lattice with distinction cost
(`SlabGap.slab_gap_explicit`, `CubicBox.box_mass_gap`), proved by Peierls contours, Dobrushin's
criterion, a supersolution clustering bound and transfer-matrix spectral bounds. The PM reading
(this lattice *is* PM's distinction substrate, `PMSubstrate.Distinctions.only_distinctions_cost`)
is an interpretation layered on top.

**Status: reached.** Everything above is proved with no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound`.

**Not pursued, by decision:** the continuum limit; SU(N) at strong coupling (a general lattice
result, not PM, and not prize-relevant); the flip-odd sector (no volume-uniform gap exists there);
tightening the `β ≥ 30` constant.

**Reopens only if** PM derives `β` at the substrate scale *and* identifies the gauge Wilson cost
with the distinction/survival cost, or an external continuum construction becomes available to
compare against.

## What the gap work exposed for PM

The ledger couplings are scale-free, but `PMConstants` compares them with running couplings at
`M_Z` (`StrongLedgerTest` notes the scale must be stated). With ordinary running, a lattice
coupling of `β ≈ 4` corresponds to a spacing of order `1/GeV`. So PM must say where its ledger
couplings live: at the substrate spacing (then the substrate spacing is about `1/GeV`, a sharp
and falsifiable claim), or read at `M_Z` by choice (then that choice is a free input). This is a
question for the physics test, not for this branch.

## Reusable lessons

- **Discreteness ⇒ volume-uniform gap.** An **integer-valued** cost with a **unique** ground state
  (up to relabeling) is gapped by at least one unit, *uniformly in volume*, and the diagonal
  transfer contracts the excited sector (`DefectGap.cost_ge_one`,
  `transfer_contracts_excitations`); the gap survives a form-bounded perturbation with `ε < m/2`
  (`GapStability.gap_pos`, `DefectGap.gap_survives_offdiagonal`). The same "discrete count +
  unique minimizer" shape appears in the framework's selection results
  (`SelectionSymmetry.unique_minimizer_fixed`, `Vacuum.least_rank_most_persistent`, E6's
  `probability_uniform_of_const_weight`) — worth reusing wherever an input is a count.
- **Complementary gap halves.** `DefectGap` (diagonal cost) and the pre-existing linearized
  Hessian/Schur gap (`SplitGap`, `VacuumSchur`, `VacuumLocalGap`, `JointVacuumGap`,
  `CompactSplitGap`) are the two halves of a transfer-matrix gap; for the distinction substrate the
  volume-uniform off-diagonal control is now supplied by the cluster expansion in `MassGap/`.
- **Cluster expansion ⇒ gap.** A weight `p^(count of local distinctions)` with `p` small gives
  contour polymers, Dobrushin convergence, a supersolution decay bound and a volume-uniform
  spectral gap (`PMAction/MassGap`, `SlabGap.slab_gap_explicit`). Reusable for any PM model whose
  weight is a power of a local event count.
- **Gap = coupling; local defects cost locally.** At `p = exp(−β)` the survival weight is the
  Gibbs density `exp(−β·cost)` (`DefectGap.survival_eq_gibbs`, `gap_eq_coupling`), so the per-tick
  gap *is* the Gibbs coupling — a general "decay rate = coupling" reading. And a defect confined to
  a region `Λ` has cost bounded by the adjacent pairs touching `Λ` (`cost_le_of_defect_subset`),
  the first step of a locality argument for the off-diagonal part.
