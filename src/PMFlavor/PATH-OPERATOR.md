# Concrete path operator

## Weights

The two link weights are fixed from the capacity ratio:

```text
w1 = 1
w2 = pmnsCapacity / ckmCapacity = 21/16
```

## Operator

```text
L = [[ 1,      -1,        0    ],
     [-1,      37/16,    -21/16 ],
     [ 0,     -21/16,     21/16 ]]
```

## Eigenbasis

Rational eigenvalues:

```text
0, 9/8, 7/2
```

Integer eigenvectors:

```text
v0 = (1, 1, 1)       eigenvalue 0
v1 = (8, -1, -7)     eigenvalue 9/8
v2 = (2, -5, 3)      eigenvalue 7/2
```

These are proved in `PathOperator.lean`:

```lean
pathOperator_mulVec_v0
pathOperator_mulVec_v1
pathOperator_mulVec_v2
```

## Fixed-weight comparison

Normalizing the ascending-eigenvalue basis `(v0, v1, v2)` and reading the
standard mixing angles gives approximately:

```text
θ12 ≈ 52.4°
θ13 ≈ 18.9°
θ23 ≈ 59.0°
```

This is large mixing.  It is closer to the PMNS sector than to CKM, but it does
not match either sector numerically.

## Verdict

The capacity-derived path operator is a genuine structural operator with a
rational spectrum.  The weights alone are **not** enough:

```text
capacity weights → large mixing
CKM requires       small mixing
```

So the next ingredient must be a hierarchical diagonal mass term (or a different
path orientation), not a fit to `V`.
