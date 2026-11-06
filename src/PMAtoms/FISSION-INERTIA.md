# Collective-inertia tests

Comparison only.  Approximate SF partial lifetimes were used; the superheavy
entries are the least certain part of the table.

## Forms tested

1. Linear fissility

```
C_f = A − k(Z²/A − x₀)
```

Works through Cf, fails for Fm/No/Rf because `C_f` becomes negative.

2. Inverse barrier / width

```
C_f = a/(x_c − Z²/A) + b
```

A quick fit to the actinides gives a steep barrier, but it still misses No-252
and Rf-256 by many orders of magnitude.

3. Fragment Q + Coulomb

The Q difference between symmetric and `Sn-132` splits is only `10⁻³–10⁻²`,
and the fragment Coulomb term is not enough to fix the superheavy scale.

## What this says

The missing object is not a scalar function of `Z²/A`.

It is a fragment-resolved barrier surface:

```
fragment pair
→ shell-corrected barrier height
→ collective inertia / width
→ channel weight
```

The actinide linear fissility is a useful effective model, but it is not the
underlying E8 barrier law.
