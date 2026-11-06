# Finite spectral beta weights

Comparison tool: `tools/spectral_beta.py`. This is not a theorem input.

For an `n×n×n` Dirichlet cube, the mode weight is

```
w(a,b,c) = exp(−λ(a,b,c))
λ = 6 − 2cos(πa/(n+1)) − 2cos(πb/(n+1)) − 2cos(πc/(n+1)).
```

Open-weight fraction below a cutoff `E`:

| n | E=2 | E=4 | E=6 | E=10 |
|---:|---:|---:|---:|---:|
| 3 | 0.452840 | 0.783118 | 0.989261 | 0.999906 |
| 4 | 0.288109 | 0.815430 | 0.979104 | 0.999982 |
| 5 | 0.452504 | 0.853439 | 0.986638 | 0.999959 |
| 6 | 0.550541 | 0.866333 | 0.982722 | 0.999933 |
| 8 | 0.552289 | 0.878052 | 0.985674 | 0.999947 |
| 10 | 0.570565 | 0.882195 | 0.985418 | 0.999949 |

The spectral fraction is not yet a lifetime: it multiplies the unknown `β·c0`.
What this table establishes is that the finite E8 spectral sum is well behaved and
that the open fraction is a smooth, cutoff-controlled number.

The candidate E8 calibration is `h = G_F²/(σ−χ) = G_F²/3`.  With `h ≈ 3.09×10⁻²⁴`
in `m_e` units, the table gives:

| fraction | implied τ_n |
|---:|---:|
| 0.288 | ≈ 1446 s |
| 0.45 | ≈ 926 s |
| 0.50 | ≈ 833 s |
| 0.55 | ≈ 757 s |

A fraction near `0.45–0.47` lands near the measured `878 s`.  This is a candidate
calibration, not a fit or a proof.
