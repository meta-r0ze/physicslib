# PMAtoms — open work (todo)

Checked results are in [`OVERVIEW.md`](OVERVIEW.md); build instructions are in
[`README.md`](README.md). This file is only open work.

The nucleus mass ledger now has the layers

```
free nucleons
− 3D packing links
− typed channel asymmetry
− cycle closure
− alpha-cluster closure
− heavy shell correction
+ charge
− even-even collective deformation (candidate)
```

The main remaining issues are the heavy deformation shape, the charge tail, and
the rate/lifetime layer.

## Honest gaps

| gap | status |
| --- | --- |
| per-link weight `πD·3/5` | closed: `(linkRowSum−1)/σ` |
| channel asymmetry `σ/ν` | closed: `boundaryWeight/(ν/2)` |
| alpha weight `Δ/D` | E8 expression; physical alpha assignment is model input |
| shell cost `Δ/(D+χ)` | E8 expression; shell assignment is model input |
| odd-A factor `3/4` | E8 expression; pairing assignment is model input |
| charge normalization | `sphereCoulombNormalized` defined; mass ledger still uses the unnormalized convention |
| `N>146` tail | deformation candidate exists but holdout even-even actinides scatter `−0.019` to `+0.018 u`; shape is not predictive yet |
| spectral Green | closed: `cubeLapN_spectralGreen` |
| 1D/3D mode theorems | closed |
| uniform odd-mode reduction | closed |
| `S(n) ~ n⁵/(16π)` | numerical evidence; asymptotic theorem open |
| nuclear lifetimes/rates | structural `MeanLife` only; no E8 clock calibration |
| electron shells | cloud exists; screening/exchange and chemistry-level shell interaction are separate |
| Aufbau order | supplied model input |
| unified system type | `Nucleon`/`Nuclide`/`Atom`/`Particle` are separate ledgers |

## 1. Heavy deformation shape

The candidate term is

```
− deformationWeight · max((Z−82)(N−126) − 82, 0)
```

for even-even nuclei, with

```
deformationWeight = shellWeight/(Δ+σ)
                  = Δ/((D+χ)(σ−χ)ν)
                  = 43/288.
```

Training set is inside `±0.008 u`, odd-A controls are fine, but holdout
even-even nuclei Pu-244/246, Cm-248, Cf-246/248, Fm-254, No-252/254, Rf-256
scatter from `−0.019` to `+0.018 u`.

Likely missing: a Z-dependent or mid-shell deformation factor, or shape
coexistence. Do **not** integrate the term into the table until the holdout
passes.

### Heavy-tail candidate ranking

Short tests on the even-even residuals after the two-shape model:

| candidate | test result | assessment |
| --- | --- | --- |
| cubic Landau / `P·(N−152)` | RMS `0.0052`, but needs a nonphysical intercept | most likely: it is the `Bβ³` term of the shape potential; coefficient ≈ `deformationWeight/ν` |
| symmetry energy `(N−Z)²/A` | RMS `0.0056`, also intercept-dominated | plausible standard liquid-drop term |
| closure at `N=152` | RMS `0.0061` | real but too sharp alone |
| distance to nearest E8 magic | RMS `0.0062` | shell-ladder effect, not an energy law |
| Z-linear deformation | RMS `0.0069` | partial, not predictive |
| Nilsson/Strutinsky | fit collapses to zero | level ordering not realistic enough |
| finite-size lattice charge | changes too slowly with A | ruled out for Cm/Cf |
| pairing factor | fixes odd-odd Md-256 only | necessary bookkeeping, not the heavy slope |
| alpha tail | untested | possible but no E8 coefficient yet |

The smooth-ledger boundary is now formalized in `NuclearRegime`: `Z=96`, `N=152` is the deformed-actinide frontier. `cm_at_frontier` and `cf_beyond_frontier` make Cm/Cf a regime change, not an outlier to be fitted. The remaining heavy work belongs to the collective/fission regime beyond that frontier. `CollectiveRegime` now supplies the lower-envelope mass, `CollectivePersists`, and the persistence/equality theorem. `alphaChannel` and `fissionChannel` now populate the collective envelope with smooth-ledger fragment masses and the E8 `shellWeight` barrier. The barrier is still schematic. `CollectiveRate` now wires barrier → hazard → `MeanLife` → `PersistsOn`, including the empty-channel indefinite-persistence case. A mass-only check shows the problem: symmetric fission fragments are already lower in the smooth ledger by `≈0.29 u`, so the lower-envelope criterion would predict immediate fission. Alpha is lower by `≈0.009 u` even with a `Δ`-scale barrier. Mass minimality alone is therefore the wrong persistence criterion for the post-frontier regime; the barrier/rate layer (`MeanLife`/`PersistenceRate`) is required. `not_collectivePersists_of_lower` records the mass-only consequence. `e8CubicPotential`/`nuclearMassPackingCubic` implement it with `cubicCoupling = deformationWeight/ν = (43/288)/16`, but the literal minimum still leaves the holdout at `≈0.0135 u`. The term is structurally E8-clean but not yet predictive.

## 2. Charge tail

The exact `3×3×3` charge response is certified, but it does not scale to heavy
nuclei by a global factor. A low-Z-anchored finite-size differential is the next
principled target. It remains an alternative explanation for the same heavy tail.

## 3. Proton-shell / deformed closure

`protonShell = 2(Δ−χ) = 82` is proved. A candidate deformed proton closure
`2(Δ+σ) = 96` is recorded, but a simple closure term is too large and
overcorrects U-238.

## 4. Spectral asymptotic (optional for the mass table)

```lean
uniformResponse_asymptotic :
  Tendsto (fun n => uniformResponse n / n^5) atTop
    (𝓝 (1 / (16 * Real.pi)))
```

The finite spectral machinery is complete; this is a genuine asymptotic analysis
theorem and is not needed for the current mass ledger.

## 5. Nuclear rates and lifetimes

`MeanLife` and `PersistenceRate` give the structural rate → lifetime step. The
missing input is the E8 per-channel rate/clock. Numeric lifetimes are deferred.

## 6. Electron cloud / chemistry pillar

The electron cloud exists as a Pauli-constrained spin-orbital set. Missing:
electron–electron screening/exchange, shell energy, and the chemistry-level
60°/tetrahedral shell interaction. This is a separate pillar from the nuclear
mass ledger.

## 7. Periodic table and unified system type

`e8p --periodic-table` still uses the leading lattice weight, not the full
nuclear mass ledger. Integrating the two-ledger mass into the table, proving
Aufbau order, and unifying `Nucleon`/`Nuclide`/`Atom`/`Particle` into one
`System` record remain open.

## Checkpoint path

PMAtoms is checkpoint-ready when:

1. `NuclearLedger` exposes one `certifiedMass` with a proved domain.
2. Candidate modules (`NuclearDeformation`, `ShapePotential`, `SingleParticle`,
   `CollectiveRegime`, `CollectiveRate`, `CollectiveE8`) are explicitly marked
   experimental and are not imported by `certifiedMass`.
3. `README`, `OVERVIEW`, `ATOM-SYSTEM`, and this file agree on certified vs
   experimental status.
4. `RESIDUALS.md` records the comparison residuals outside the theorem tree.
5. `./build.sh fast PMAtoms`, `./build.sh audit`, and `./build.sh e8p` pass.
   Checkpoint decision: e8p keeps the leading lattice weight; wiring
   `certifiedMass` into the printed table is deferred.
6. A git checkpoint records the job/declaration counts.

Not required for the checkpoint: solving Cm/Cf, the E8 clock/barrier
normalization, alpha preformation, fission fragment asymmetry, the spectral
asymptotic, or the electron/chemistry pillar.
