# The atom system

This is the narrative map of the PM atom ladder. It is not the theorem index —
that is [`OVERVIEW.md`](OVERVIEW.md) — and it is not the open-work list — that is
[`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md). It explains **how the pieces fit**.

## 1. Ownership

The substrate owns the E8 record and its selection premises:

```
PMSubstrate.E8Values
  D = 4, Δ = 43, ν = 16, σ = 5, χ = 2
```

The atom ladder owns everything derived from those values:

```
PMAtoms.E8AtomValues
  Δ + σ = (σ−χ)ν
  2(Δ−χ) = 82
  (σ−χ)(Δ−1) = 126
  2(Δ+σ) = 96
  (σ−χ)Δ + (ν+σ+χ) = 152
  D(Δ+σ−χ) = 184
  (D+χ)(σ−χ)ν = 288
```

Atom identities are proved in the atom library, not re-proved in the substrate.

## 2. The ladder

```
nucleon
  → link graph
  → 3D packing
  → typed channels
  → independent closures
  → alpha clusters
  → shell corrections
  → charge ledger
  → collective/fission regime
```

Each layer is a count. The mass is the ledger of those counts.

## 3. What is certified

The certified core is:

- nucleon charge/baryon from substrate channels
- 3+1 link split
- H-3/He-3/He-4 typed counts
- cubic packing count `E = 3n²(n−1)` and surface/volume law
- `3×3×3` interior-vertex selection
- typed `pp/pn/nn` channel partition and mean-field counts
- closure rank
- alpha-cluster phase/surviving-budget count
- E8 magic ladder and shell occupations
- exact `2×2×2` and `3×3×3` lattice Green functions
- `cube3Lap_green`
- `cubeLapN_spectralGreen`
- sine orthogonality and uniform odd-mode reduction
- Cm/Cf regime boundary

The certified mass function is `NuclearLedger.certifiedMass`, valid on `certifiedDomain = deformedFrontier`. The certified mass terms are:

```
free nucleons
− 3D packing links
− typed channel asymmetry
− cycle closure
− alpha-cluster closure
− E8 shell correction
+ charge
```

## 4. What is a model identification

These are E8 expressions, but the physical assignment is a model input:

- `packingWeight = πD·(σ−χ)/σ`
- `packingChannelAsymmetry = σ/ν = boundaryWeight/(ν/2)`
- `alphaClosureWeight = Δ/D`
- `shellWeight = Δ/(D+χ)`
- odd-A shell factor `(D−1)/D = 3/4`

They are not fitted constants, but they are identifications of which E8 ratio
pays which physical cost.

## 5. Experimental / candidate modules

These are exploratory and are **not** part of the certified mass column:

- `NuclearDeformation`: even-even collective deformation, Z-factor, pairing factor
- `ShapePotential`: Landau `Aβ²+Bβ³+Cβ⁴` and E8 control coefficients
- `SingleParticle`: schematic `nlj` orbitals, Nilsson energies, Strutinsky scaffold
- `CollectiveRegime`: alpha/fission channel envelope
- `CollectiveRate`: barrier → hazard → mean-life scaffold

Their status is:

| module | status |
| --- | --- |
| `NuclearDeformation` | candidate; training fit good, holdout fails `±0.01 u` |
| `ShapePotential` | structural; literal Landau minima not predictive |
| `SingleParticle` | structural; Nilsson/Strutinsky not predictive yet |
| `CollectiveRegime` | structural; mass envelope only |
| `CollectiveRate` | structural; barrier normalization open |

## 6. The boundary

The smooth spherical/deformed ledger is valid through

```
Z = 96 = 2(Δ+σ)
N = 152 = (σ−χ)Δ + (ν+σ+χ)
```

`NuclearRegime` proves:

```
cm_at_frontier     : deformedFrontier 96 148
cf_beyond_frontier : ¬ deformedFrontier 98 154
```

Cm sits on the frontier; Cf is beyond it. The Cm/Cf residual is a **regime
change**, not an outlier to be fitted away.

## 7. What the model does not claim

The atom ladder does **not** currently claim:

- a derived substrate record (the `baseline` is still a PMSubstrate premise)
- a derived nuclear rate/clock
- numeric nuclear lifetimes
- a complete fission/alpha barrier from E8
- electron screening/chemistry-level shell interaction
- a unique periodic-table valley from the mass ledger alone

Those are open, and some are PMSubstrate or separate-pillar work.

## 8. How to read a residual

A residual is meaningful only with its regime:

```
smooth ledger residual       → shell/packing/charge bookkeeping
post-frontier residual       → collective/fission regime
```

Do not combine the Cm/Cf residual with the smooth fit. They are different
regimes.

## 9. e8p

`e8p` reports values, comparisons and provenance. The atom mass ledger is not yet
fully wired into the printed periodic table; the current table uses the leading
lattice weight. The eventual table should show:

```
Z, N, A, regime, m_E8, m_iso, residual
```

with the regime column marking the Cm/Cf boundary. Checkpoint decision: e8p is **not** wired to `certifiedMass` yet; the printed table still shows the leading lattice weight.

## 10. Reading order

1. [`README.md`](README.md) — modules and build
2. [`OVERVIEW.md`](OVERVIEW.md) — theorem index
3. [`REVIEW-AND-NEXT.md`](REVIEW-AND-NEXT.md) — open work
4. this file — the narrative
5. `NUCLEAR-GRAPH.md`, `nuclei_arrangement.md` — graph/line details
6. `E8AtomValues.lean` — E8 ownership
7. `NuclearRegime.lean` — the boundary

## 11. The honest summary

The nucleus is a **persistence graph**:

```
links → typed channels → 3D packing → closures
      → alpha clusters → shells → charge → collective regime
```

The mass is the ledger of those counts. The model is strong through the deformed
actinide frontier, and Cm/Cf mark where the smooth ledger hands off to the
collective/fission regime. That boundary is itself E8 data.
