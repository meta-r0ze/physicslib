# Alpha lifetime comparison

Comparison data only. Model uses the finite alpha channel (`AlphaFinite`) and the frontier-local E8 width:

```
B = (43/14)·Z/√Q + (σ/2)·d
F = exp(−ν/(d+1))
τ ∝ exp(B)/F
```

Reference is U-238. `d` is the Euclidean daughter distance to the E8 magic
ladder. Measured half-lives are frozen comparison inputs.

| parent | daughter `d` | `F` | model τ/τ_U238 | observed τ/τ_U238 | model/obs |
|---|---:|---:|---:|---:|---:|
| U-234 | 13.42 | 0.330 | 8.16 | 5.50×10⁻⁵ | 1.5×10⁵ |
| U-235 | 12.53 | 0.307 | 5.44 | 1.58×10⁻¹ | 34 |
| U-238 | 10.00 | 0.234 | 1 | 1 | 1 |
| Pu-238 | 10.77 | 0.257 | 1.75×10⁻⁴ | 1.96×10⁻⁸ | 8.9×10³ |
| Pu-239 | 9.85 | 0.229 | 3.38×10⁻⁴ | 5.40×10⁻⁶ | 63 |
| Pu-240 | 8.94 | 0.200 | 3.67×10⁻⁵ | 1.47×10⁻⁶ | 25 |
| Cm-244 | 6.32 | 0.113 | 3.57×10⁻⁹ | 4.05×10⁻⁹ | 0.88 |
| Cm-246 | 4.47 | 0.0537 | 2.02×10⁻⁹ | 1.07×10⁻⁶ | 0.002 |
| Cf-250 | 2.00 | 0.00483 | 3.98×10⁻¹² | 2.93×10⁻⁹ | 0.001 |
| Cf-252 | 0.00 | 1.13×10⁻⁷ | 3.05×10⁻¹⁰ | 5.92×10⁻¹⁰ | 0.52 |
| Fm-252 | 2.83 | 0.0153 | 3.95×10⁻¹⁴ | 6.48×10⁻¹³ | 0.061 |

## Reading

The closure hindrance fixes the Cm-244/Cf-252 pair near the deformed frontier.
It does **not** describe U-234, Pu-238, Cm-246, or Cf-250.  The failure is not a
small normalization: the required correction is several orders of magnitude and
changes sign across the chain.

So the current E8 alpha width is **frontier-local**, not a universal
Geiger--Nuttall law.  The likely missing physics is a Q-dependent preformation
or a regime-dependent barrier coefficient; the constant Geiger coefficient
`43/14` is not enough by itself.

## cKf absolute scale

Using the E8 ledger

```
c = 1
K = alphaCapacity = min(Z,N)/2
f = 1/Δ = 1/43
```

the predicted absolute lifetimes are:

| parent | predicted τ | measured τ | ratio |
|---|---:|---:|---:|
| U-238 | ≈ 1.05×10³³ s | 1.41×10¹⁷ s | ≈ 7.5×10¹⁵ |
| Cm-244 | ≈ 3.59×10²⁴ s | 5.71×10⁸ s | ≈ 6.3×10¹⁵ |
| Cf-252 | ≈ 3.02×10²³ s | 8.35×10⁷ s | ≈ 3.6×10¹⁵ |

The relative ordering is roughly right, but the absolute scale is too long by
about `10¹⁵`.

So `cKf` alone is not enough: the barrier exponent is being used in the wrong
energy unit, or the collective workload `K_alpha` is not the alpha capacity.
The next fix is in the barrier normalization, not in the attempt frequency.

## Leading E8 cost scale

Candidate E8 scale:

```
C_alpha = Δ²/(ν+σ) = 1849/21 ≈ 88.05
```

With `cKf` and `exp(−C_alpha)`:

| parent | predicted τ | measured τ |
|---|---:|---:|
| U-238 | ≈ 2.09×10¹⁷ s | 1.41×10¹⁷ s |
| Cm-244 | ≈ 2.00×10¹⁷ s | 5.71×10⁸ s |
| Cf-252 | ≈ 1.96×10¹⁷ s | 8.35×10⁷ s |

The leading scale lands near U-238 but has no Q dependence, so Cm/Cf are far too
long. The next term must be a Q-dependent E8 correction, not a new attempt
frequency.

## Q-dependent E8 cost

Candidate:

```
C_alpha(Q) = (Δ/(σ+χ))·Z/√Q − (Δ/2)·σ
           = (43/7)·Z/√Q − 107.5
```

Results:

| parent | C_alpha | predicted τ | measured τ | ratio |
|---|---:|---:|---:|---:|
| U-238 | 88.01 | 2.00×10¹⁷ s | 1.41×10¹⁷ s | 1.42 |
| Cm-244 | 66.01 | 5.39×10⁷ s | 5.71×10⁸ s | 0.094 |
| Cf-252 | 65.09 | 2.11×10⁷ s | 8.35×10⁷ s | 0.252 |

This fixes the U-238 scale and gives a decreasing lifetime with increasing Q, but
Cm/Cf are now too short. The Q coefficient is the next structural question.

## Improved E8 Q cost

Candidate:

```
C_alpha(Q) = (Δ/(D+2χ))·Z/√Q − (2Δ−χ)
           = (43/8)·Z/√Q − 84
```

| parent | C_alpha | predicted τ | measured τ | ratio |
|---|---:|---:|---:|---:|
| U-234 | 76.40 | 1.82×10¹² s | 7.75×10¹² s | 0.23 |
| U-235 | 79.44 | 3.79×10¹³ s | 2.22×10¹⁶ s | 0.002 |
| U-238 | 87.07 | 7.81×10¹⁶ s | 1.41×10¹⁷ s | 0.55 |
| Pu-238 | 68.72 | 8.24×10⁸ s | 2.77×10⁹ s | 0.30 |
| Pu-239 | 73.70 | 1.20×10¹¹ s | 7.61×10¹¹ s | 0.16 |
| Pu-240 | 73.54 | 1.02×10¹¹ s | 2.07×10¹¹ s | 0.49 |
| Cm-244 | 67.83 | 3.32×10⁸ s | 5.71×10⁸ s | 0.58 |
| Cm-246 | 73.64 | 1.11×10¹¹ s | 1.50×10¹¹ s | 0.74 |
| Cf-250 | 69.34 | 1.47×10⁹ s | 4.13×10⁸ s | 3.56 |
| Cf-252 | 67.02 | 1.44×10⁸ s | 8.35×10⁷ s | 1.72 |
| Fm-252 | 59.66 | 9.03×10⁴ s | 9.14×10⁴ s | 0.99 |

Most entries are within a factor of four. U-235 is the clear outlier. This is a
strong E8 candidate, but not yet a proof: the cost form must be derived from the
collective link counting, not selected from the table.

## Residual diagnosis

Quick single-feature fits to `ln(model/observed)` using the `(43/8)Z/√Q − 84`
cost:

| feature | RMS | verdict |
|---|---:|---|
| odd-A | 1.21 | best single feature, but U-235 still outlier |
| `N−152` | 1.37 | weak |
| `|N−152|` | 1.35 | weak |
| daughter distance `d` | 1.36 | weak |
| `Z−82` | 1.46 | weak |
| `Q` | 1.60 | not the missing variable |
| fissility `Z²/A` | 1.56 | weak |

Even-even residuals average about `−0.33`; odd-A residuals average about
`−4.1`.  But the odd-A penalty fitted globally (`≈−3.2`) fixes U-235 and spoils
Pu-239.  So the missing term is not a universal odd-A shift.

The strongest interpretation is a **single-particle / spin-parity hindrance**
term, not another smooth E8 cost.

## Spin-parity diagnostic

Using the actual ground-state assignments:

```
U-235 7/2− → Th-231 5/2+   (spin mismatch 2, parity change 1)
Pu-239 1/2+ → U-235 7/2−   (spin mismatch 6, parity change 1)
```

`AlphaHindrance` gives:

```
U-235  hindrance units = 3
Pu-239 hindrance units = 7
```

Fitting U-235 alone needs a scale near `2`, but that gives Pu-239 a hindrance
near `14`, far more than its residual requires.  So a single spin-parity scale
cannot fix both odd-A outliers.  The missing term is a full Nilsson/level
hindrance, not just `Δj + parity`.

## Blocking hindrance test

`alphaBlockingHindrance` adds `log(2)` for any odd-A parent.  Both U-235 and
Pu-239 receive the same `+0.693`.  After that correction U-235 is still far too
short and Pu-239 is only slightly improved.  Blocking alone is therefore not
the missing term.

## Where the smooth list ends

The quick tests rule out, as the leading missing effect:

- a global factor of 4,
- a universal odd-A shift,
- simple `Z/√Q` refitting,
- surface/channel-count terms,
- a smooth daughter-distance term.

What remains is the actual **level/configuration hindrance**.

## Configuration-mixing correction

Two-level Nilsson mixing with E8 parameters:

```
κ = 1/ν = 1/16
μ = χ/σ = 2/5
δ = 1/σ = 1/5
hindrance = σ/(|ΔE| + 1/χ)
```

applied only to odd-A parents.

| parent | hindrance | new ratio model/obs |
|---|---:|---:|
| U-235 | 6.36 | 0.987 |
| Pu-239 | 1.85 | 1.007 |

Even-even entries are unchanged. This fixes both odd-A outliers without touching
the even-even chain. The E8 Nilsson parameters and mixing form are still a
candidate model, not a first-principles derivation.

## Non-zero mixing V

With `V = κμδ = 1/200`:

| parent | hindrance `V=0` | hindrance full | relative shift |
|---|---:|---:|---:|
| U-235 | 6.361323 | 6.360616 | −0.011% |
| Pu-239 | 1.850481 | 1.850473 | −0.0004% |

The tiny size is expected: the dressed gap changes by `≈2V²/ΔE`, which is of
order `10⁻⁵`.  The scalar `V=0` formula is therefore an excellent approximation.
