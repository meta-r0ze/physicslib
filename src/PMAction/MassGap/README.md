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
| `GapChain` | Assembly: `contour_decay` (explicit, volume-uniform, `θ = 4Kq/(1−2q) ≤ 8Kq`) and the conditional gap `gap_of_euclidean_decay`. |

## Status

Proved: everything above. Open: the contour representation that turns `contour_decay` into
`GapChain.EuclideanDecay` for the PM spacetime transfer matrix (see `GapChain`'s docstring).
Scope: the contour route gives a gap only for discrete link values (`PeierlsDichotomy`); it is
not the Clay statement for continuous `SU(N)`.
