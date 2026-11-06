# Fission scale test

Comparison only.

Candidate scale:

```
C_f = Δ²/(ν+D+σ+χ) = 1849/27 ≈ 68.48
```

With the alpha `cKf` attempt:

| parent | predicted τ | measured spontaneous-fission τ |
|---|---:|---:|
| U-238 | ≈ 6.6×10⁸ s | ≈ 2.6×10²⁴ s |
| Cf-252 | ≈ 6.2×10⁸ s | ≈ 2.7×10⁹ s |

The scale has no fissility/Q dependence, so it cannot separate U-238 from Cf-252.
The next term must be a fissility-dependent E8 barrier, not another attempt
frequency.

## Fissility candidate test

A simple E8 fissility cost

```
C_f = Δ²/(ν+D+σ) − (Δ/D)·(Z²/A − (Δ−D))
```

gives:

| parent | Z²/A | C_f | predicted τ | measured SF τ |
|---|---:|---:|---:|---:|
| U-238 | 35.56 | 113.99 | 3.85×10²⁸ s | ≈10²⁴ s |
| Cf-252 | 38.11 | 86.60 | 4.59×10¹⁶ s | ≈2.7×10⁹ s |

This is much too long and still does not separate the two nuclei correctly.
A simple one-term fissility correction is not enough.  The next object needed is
the fragment barrier distribution, not another global fissility coefficient.

## E8 fissility + N=152 shell correction

Leading cost:

```
C_f = Δ²/(ν+D+σ+χ) − σχ·(Z²/A − (Δ−D))
    = 1849/27 − 10·(Z²/A − 39)
```

Above `N=152`, subtract the E8 shell weight `Δ/(D+χ)=43/6`.

| parent | C_f | predicted τ | measured SF τ | ratio |
|---|---:|---:|---:|---:|
| U-238 | 102.85 | 5.60×10²³ s | 2.59×10²³ s | 2.17 |
| Pu-240 | 90.31 | 1.97×10¹⁸ s | 3.60×10¹⁸ s | 0.55 |
| Cm-244 | 80.78 | 1.39×10¹⁴ s | 4.26×10¹⁴ s | 0.33 |
| Cf-250 | 74.32 | 2.14×10¹¹ s | 4.10×10¹¹ s | 0.52 |
| Cf-252 | 70.20 | 6.4×10⁹ s | 2.68×10⁹ s | 2.4 |

All five are within a factor of ~2.4.  This is a strong candidate barrier model,
not yet a first-principles derivation.

## Superheavy extrapolation test

Applying the same linear fissility formula above Cf:

| parent | Z²/A | C_f | predicted τ | approximate SF τ |
|---|---:|---:|---:|---:|
| Fm-254 | 64.94 | −190.9 | ≈2.6×10⁻¹⁰⁴ s | ≈1.2×10⁴ s |
| No-252 | 69.36 | −235.1 | ≈1.8×10⁻¹²³ s | ≈2.4 s |
| Rf-256 | 71.16 | −253.1 | ≈2.8×10⁻¹³¹ s | ≈6.5×10⁻³ s |

The linear fissility cost becomes negative and fails completely.

So the actinide fit is real, but it does not extrapolate to the superheavies.
The next object is not another linear fissility term. It must be a nonlinear
barrier / fragment-distribution model.

## N=152 shell trigger

Verified:

```
Cf-250 (N=152): no shell correction
Cf-252 (N=154): subtract 43/6
Fm-252 (N=152): no shell correction
Fm-254 (N=154): subtract 43/6
```

This confirms the trigger is the `N=152` closure, but it is not enough for the
superheavy region.
