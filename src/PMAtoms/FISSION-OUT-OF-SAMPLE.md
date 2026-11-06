# Fission out-of-sample check

Approximate SF partial lifetimes; comparison only.

The full-yield model with scale `Δ²/(D+σ)=1849/9` was tested outside the original
five nuclei.

| parent | predicted τ | approximate SF τ | ratio |
|---|---:|---:|---:|
| U-234 | 9.27×10²⁰ s | 5.05×10²⁴ s | 0.00018 |
| Pu-242 | 2.86×10¹⁹ s | 2.15×10¹⁸ s | 13.3 |
| Cm-246 | 1.92×10¹⁵ s | 4.73×10¹⁴ s | 4.05 |
| Cf-250 | 1.27×10¹¹ s | 4.10×10¹¹ s | 0.31 |

The fit is not universal.  U-234 is the strongest failure: the linear fissility
term predicts it should fission faster than U-238, while the approximate SF data
say the opposite.

This is either a data/branching issue or a missing N-dependent shell term near
`N=142`.  The one-shot yield scale should not be promoted until this is resolved.

## Checkpoint decision

The one-shot fission scale is a candidate, not a certified universal law.  The
five-nucleus surface is retained as an effective model; U-234/Pu-242 remain an
open shell-structure problem.
