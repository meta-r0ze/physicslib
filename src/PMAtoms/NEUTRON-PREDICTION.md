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

**Proved enclosure.** `PMHadrons.neutronLifetimeCorrectedSeconds_bounds`:
`877.1 s < τ_n < 877.2 s` (the margin-corrected lifetime, exact cutoff `m_n − m_p`, `r = e^{−√2}` to
`10⁻⁷`, `G_F` and the unit inputs `m_e`, `ħc`). Against the PDG 2024 average `878.4 ± 0.5` s it is
`−2.5σ` (`e8p` row `neutron_lifetime_predicted_s`).

This is a candidate E8 prediction, not a fit. The finite spectral fraction is an
external comparison calculation; the Lean side formalizes the cutoff, fraction
expression, margin factor, and lifetime expression.

## Update: one template for π, K and n

The `41/43` above is the Governor's surviving-phase fraction, and it is applied here as a factor
above one on the rate, which a Governor cannot be
(`PMHadrons.DecayInstantiation.neutronCorrected_governor_gt_one`). Put in the same
`DecayChannel` template as the pion (`|V_ud|²` in map, shared margin `R` with `|V_ud|²R = 32/33`,
no Governor), the neutron is `948.69–948.70 s` (`neutronLifetimeUnifiedSeconds_bounds`), +8.0%.
The 8.0% is the neutron-only Coulomb, `g_A` and low-energy radiative pieces
(`PMHadrons/REVIEW-AND-NEXT.md` §0).

