# Neutron beta prediction

Comparison calculation, not a theorem input.

Inputs:

```
minimal cube n = 3        (cube_interior_iff)
cutoff E = m_n − m_p      (exact endpoint)
spectral fraction f       ≈ 0.452840
hazard h = G_F²/(σ−χ)     ≈ 3.09×10⁻²⁴
margin factor 1−χ/Δ        = 41/43
```

Results:

| quantity | value |
|---|---:|
| raw finite-spectral prediction | ≈ 920 s |
| with E8 margin `41/43` | ≈ 877.2 s |
| measured | ≈ 878 s |

The corrected prediction is within about `0.1%` of the measured lifetime.

This is a candidate E8 prediction, not a fit. The finite spectral fraction is an
external comparison calculation; the Lean side formalizes the cutoff, fraction
expression, margin factor, and lifetime expression.
