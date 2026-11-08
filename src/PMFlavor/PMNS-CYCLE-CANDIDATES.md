# PMNS cycle candidates

Exploration only.  The CKM operator is fixed.  The PMNS cycle adds a third link
between the outer path nodes with weight `w3` and phase `φ`.

Baseline:

```text
w1 = 1
w2 = 21/16
```

Candidate weights are E8 invariants, not fitted numbers.

## Ranked `w3` candidates

| rank | `w3` | value | meaning |
|---:|---|---:|---|
| 1 | `ν/(ν+σ)` | 16/37 ≈ 0.7619 | CKM capacity fraction |
| 2 | `σ/(ν+σ)` | 5/37 ≈ 0.1351 | colour fraction of total capacity |
| 3 | `χ/σ` | 2/5 = 0.4 | colour-to-generation ratio |
| 4 | `1/σ` | 1/5 = 0.2 | inverse colour |
| 5 | `(σ−χ)/ν` | 3/16 = 0.1875 | weak channels per generation |
| 6 | `χ/ν` | 1/8 = 0.125 | closure per generation |
| 7 | `σ/Δ` | 5/43 ≈ 0.1163 | margin per clock tick |
| 8 | `D/Δ` | 4/43 ≈ 0.0930 | spacetime per clock tick |
| 9 | `1/ν` | 1/16 = 0.0625 | inverse generation capacity |
| 10 | `χ/(ν+σ)` | 2/37 ≈ 0.0541 | closure per total capacity |

## Ranked phase candidates

`φ` is quoted in turns; `φ = 2π t`.

| rank | turns `t` | phase | meaning |
|---:|---:|---:|---|
| 1 | `σ/Δ` | 5/43 | margin per clock tick |
| 2 | `(σ−χ)/Δ` | 3/43 | weak-channel margin per tick |
| 3 | `1/ν` | 1/16 | one generation phase |
| 4 | `1/(ν+σ)` | 1/37 | total-capacity phase |
| 5 | `1/Δ` | 1/43 | one tick |
| 6 | `χ/Δ` | 2/43 | closure per tick |
| 7 | `D/Δ` | 4/43 | spacetime per tick |
| 8 | `1/σ` | 1/5 | colour phase |
| 9 | `1/χ` | 1/2 | half-turn |
| 10 | `1/(σ−χ)` | 1/3 | weak-channel phase |

## Best E8 combination

The best candidate from the scan is:

```text
w3 = ν/(ν+σ) = 16/37
φ  = 2π σ/Δ = 10π/43
D  = (m_low², m_high², m_high²)
```

Predicted angles:

```text
θ12 ≈ 28.84°
θ13 ≈ 7.89°
θ23 ≈ 49.12°
```

So `θ23` and `θ13` are close, while `θ12` is about 5° low.

## Second candidate

```text
w3 = σ/(ν+σ) = 5/37
φ  = 2π(σ−χ)/Δ = 6π/43
D  = (m_low², (m_low²+m_high²)/2, m_high²)
```

Predicted angles:

```text
θ12 ≈ 28.67°
θ13 ≈ 8.21°
θ23 ≈ 43.79°
```

## Verdict

The cycle link is the right structural direction.  The leading E8 candidate is

```text
w3 = 16/37,  φ = 10π/43,  heavy-pair diagonal.
```

It fixes `θ23` and `θ13` but leaves `θ12` low.  The next check should vary only
the PMNS mass pattern, keeping `w3` and `φ` at their E8 values.
