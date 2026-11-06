# Alpha lifetime comparison

Comparison data only. Model uses the frontier-local E8 alpha width:

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
