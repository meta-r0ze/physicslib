# Fragment-resolved fission tests

Comparison only.  The E8 mass ledger was evaluated for symmetric and `Sn-132`
asymmetric splits.

## Q test

| parent | symmetric Q | `Sn-132` Q |
|---|---:|---:|
| Fm-254 | 596.677 m_e | 596.671 m_e |
| No-252 | 630.843 m_e | 632.079 m_e |
| Rf-256 | 663.097 m_e | 665.318 m_e |

The Q differences are tiny.  Q alone does not select the `Sn-132` channel; the
effect is at the per-mille level for Fm-254 and order 0.3% for Rf-256.

## Coulomb-resolved test

Adding a fragment Coulomb cost `Z₁Z₂/(A₁^{1/3}+A₂^{1/3})` to the E8 fissility
cost makes the superheavy cost positive, but the predicted lifetimes are still
too long by roughly `10⁶–10⁸`.

## Verdict

What works:

```
actinide fissility slope
N=152 shell trigger
```

What does not yet work:

```
superheavy extrapolation
fragment Q selection
fragment Coulomb alone
```

The next missing object is the collective inertia / barrier width, not another
Q term.

## Corrected-sign surface

The closed `Sn-132` channel should **lower** the barrier:

```
C_channel = C_fissility − shellGain(Sn-132) + (1/Δ)·Coulomb
```

with:

```
shellGain = Δ/(D+χ) = 43/6
Coulomb   = chargeCoupling·Z₁Z₂/(A₁^{1/3}+A₂^{1/3})
```

Results:

| parent | predicted τ | measured-ish τ | ratio |
|---|---:|---:|---:|
| U-238 | 2.23×10²³ s | 2.59×10²³ s | 0.86 |
| Cf-252 | 2.94×10⁹ s | 2.68×10⁹ s | 1.10 |
| Fm-254 | 1.29×10⁴ s | 1.16×10⁴ s | 1.10 |
| No-252 | 0.107 s | ≈2.4 s | 0.044 |
| Rf-256 | 8.7×10⁻⁶ s | ≈6.5×10⁻³ s | 0.0014 |

U-238, Cf-252, and Fm-254 are within 15%. The superheavy No/Rf entries are
still too short, so an additional superheavy hindrance is needed.

## Superheavy governor

E8 threshold:

```
Z₀ = 2Δ + 2σ + 2χ = 100
```

Governor cost:

```
C_gov = χ · max(Z − Z₀, 0)
```

Adding this to the fragment surface:

| parent | new ratio model/obs |
|---|---:|
| U-238 | 0.86 |
| Cf-252 | 1.10 |
| Fm-254 | 1.10 |
| No-252 | 2.39 |
| Rf-256 | 4.04 |

All five are now within a factor of about four.  The No/Rf data are the least
certain, but the correction is E8-clean and does not disturb the actinides.

## Final yield-weight check

The fragment weight must depend on the **light fragment** closure, not on the
complement:

```
w(s) = exp(−(shellWeight/Δ)·(d_light))
     = exp(−d_light/6)
```

The absolute weights are used directly; normalizing them is not the physical
rate.

Result:

| parent | model/obs |
|---|---:|
| U-238 | 0.86 |
| Cf-252 | 1.09 |
| Fm-254 | 1.10 |
| No-252 | 2.39 |
| Rf-256 | 4.03 |

So the light-fragment yield weights preserve the five-nucleus surface and keep
all tested cases within a factor of about four.
