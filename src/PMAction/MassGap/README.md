# PMAction/MassGap — the gap half of the Yang–Mills branch

The existence/continuity half lives in `PMAction` proper (`LatticeGibbs`,
`ReciprocalReflection`, `OsterwalderSchrader`, `LatticeSiteAction`, …). This folder is the
**gap** half. Lean source is the ground truth; this file is a map.

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
| `SlabGap` | **The gap**: in the flip-even sector of `T²`, every eigenvalue is `≤ μ²Λ` or equals the top `Λ` (eigenvector seen by `v₀`); the even top is simple. Uniform in volume and slab length. |

## Status

Proved, no `sorry`: everything above. The chain closes in `SlabGap.slab_gap`: for the PM transfer
matrix `T` on a slab, in the low-cost regime (`SlabGap.Regime`: the `slab_clustering` conditions
on `q`, `μ < 1`, `D`), the flip-even spectrum of `T²` has a simple visible top `Λ > 0` and every
other even eigenvalue is `≤ μ² Λ`, with `μ` fixed by `q` and `D` alone.

Premises and scope (for review):
- `Regime.degree`: the plaquette-graph degree of the slab is `≤ D` for every slab length (true
  geometrically; taken as a hypothesis, not proved).
- The gap is for the flip-even sector. The odd sector (tunnelling between the two vacua) is not
  claimed.
- Discrete (`ℤ/2`) distinctions only: `PeierlsDichotomy` shows `U(1)` has no Peierls condition.
  This is not the Clay statement for continuous `SU(N)`.
