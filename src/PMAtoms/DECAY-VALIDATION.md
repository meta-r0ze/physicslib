# Frozen decay validation table

Comparison values are external; model values are E8-based unless marked.

## Elementary particles

| decay | model | comparison | status |
|---|---:|---:|---|
| n → p e ν̄ | 877.2 s | 878 s | E8 prediction |
| μ → e ν ν̄ | 2.187×10⁻⁶ s | 2.197×10⁻⁶ s | E8-input / finite channel |
| τ → μ ν ν̄ | ≈2.9×10⁻¹³ s | 2.90×10⁻¹³ s | E8 masses + supplied B_e |
| π⁺ → μ⁺ν | 2.52×10⁻⁸ s | 2.60×10⁻⁸ s | E8 fπ |
| K⁺ → μ⁺ν | ≈2.0×10⁻⁸ s | 1.95×10⁻⁸ s | E8 fK + Vus |
| π⁰ → γγ | ≈8.46×10⁻¹⁷ s | 8.52×10⁻¹⁷ s | E8 fπ + anomaly factor |
| proton | stable | stable | structural |
| neutrino | stable | stable | structural |

## Alpha

The alpha table is in `ALPHA-TESTS.md`.  Even-even emitters are within a small
factor; U-235/Pu-239 are fixed by the E8 two-level mixing term.

## Fission

The fission tables are in `FISSION-TESTS.md`, `FISSION-RESOLVED.md` and
`FISSION-OUT-OF-SAMPLE.md`.

Original five:

```
U-238, Cf-252, Fm-254, No-252, Rf-256
```

are within a factor of about 1.6.  U-234 and Pu-242 are fixed by the E8
`N=142/148` subshell costs.

## Labels

```
prediction       E8 value before comparison
candidate        E8 form selected/validated after data
calibrated       uses a measured reference
structural       channel/identity only
blocked          missing E8 input
```
