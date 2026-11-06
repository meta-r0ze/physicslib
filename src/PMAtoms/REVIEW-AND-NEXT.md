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

## 4b. Neutrino decay

The particle ledger treats neutrinos as massless, with no channel lighter than
zero.  `neutrino_stable` and `antineutrino_stable` are proved in
`PMAtoms/Particle.lean`.  There is no neutrino decay width or lifetime, no
neutrino mass ordering beyond the oscillation mixing, and no sterile-decay
channel.  Neutrino **oscillation** is in `PMFlavor.PMNS`; it is not decay.
A massive-neutrino decay channel would require a new mass ledger and is not
currently modeled.

## 4c. Regime-aware decay selection

`NuclearDecay.nuclearLedgerKind` selects the smooth ledger through the deformed
frontier and the collective ledger beyond it.  `regimePersists` is the
regime-aware criterion: mass-allowed for Cm-244, collective envelope for Cf-252.
`cm_regimePersists_iff` and `cf_regimePersists_iff` make the split explicit.
`smooth_regimePersists_iff` and `collective_regimePersists_iff` are the general
decision rules; `nuclearExits` is the β±/α/fission exit table with Q and barrier; `nuclearExitChannels` converts it to the `CollectiveChannel` form used by the rate layer; `cm/cf_exitTable_regimePersists_iff` and the alpha variants apply the rule to the actual exit table.

## 5. Nuclear rates and lifetimes

The allowed beta Coulomb factor is now `FermiFunction.fermiFunction` with
`fermiFunction_pos` and `fermiFunction_ge_one`.  The physical integrand contains
`F·p`, not `F`; this product is finite at threshold.  `fermiMomentumFactor`
records that product and `fermiMomentumFactor_pos` proves positivity.
`one_sub_exp_neg_ge` and `fermiMomentumFactor_le` show the product is bounded by
`p + 2πZαE`, so the threshold is integrable in the physical variable.  The exact
three-body Dalitz density and the transport of this bound through the full
measure remain open.  The E8-native alternative is `BetaLattice`: a finite
family of open modes with the `RateModel` cost rate, replacing the continuum
Dalitz measure.  `betaSpectralWeight = exp(−λ)` now supplies a spectral Boltzmann weight, and
`betaSpectralRate` sums those weights over a chosen mode subset.  `betaOpenModes`
selects modes below an energy cutoff and `betaSpectralRateCutoff` is positive for
a nonempty cutoff.  What remains is the numerical spectral sum and the neutron
benchmark comparison.  The spectral rate is bounded by `β c0`, so the lifetime
is bounded below by `1/(β c0)`; the open task is the actual spectral sum.

`MeanLife` and `PersistenceRate` give the structural rate → lifetime step. The
missing input is the E8 per-channel rate/clock. Numeric lifetimes are deferred.

Candidate: `alphaBarrierShellPreformed = alphaBarrierGeiger + (σ/2)·d`, with
`d` the Euclidean daughter distance to the E8 magic ladder.  This is the first
E8 preformation term with the correct Cm/Cf/U ordering; it still needs an
independent test and a derivation of the absolute attempt frequency.  The
reference-width model of Paper 5 supplies the natural next correction:
`Γ = Γ₀·P·F·exp(−B)`, where `F` is phase space/hindrance; reducing `F`
lengthens the lifetime, which is the direction needed for Cf-252.  The E8
`F` is `exp(−ν/(d+1))`; it is strong enough at the double closure and keeps the
single-closure Cm case in range.  The simpler open fraction `(d+1)/(d+ν)` is
recorded but too weak.


### Neutron prediction

`NeutronPrediction` fixes the minimal cube `n=3` and the exact endpoint
`m_n−m_p`.  With `f ≈ 0.452840`, `h = G_F²/(σ−χ)`, and the E8 margin factor
`1−χ/Δ = 41/43`, the corrected lifetime is `≈877.2 s`, within `0.1%` of the
measured `878 s`.  The off-diagonal carrier entries vanish by
`weakCarrierOperator_offdiag_zero`; the numerical fraction remains a comparison
calculation, not a theorem input.

### Finite alpha channel

`AlphaFinite` applies the same finite-channel form as beta: `rate = attempt · P ·
F · exp(−B)`.  `alphaFiniteLifetime_ratio` proves the unknown attempt frequency
cancels in relative lifetimes.  `alphaAttempt` now supplies the E8 `cKf` form:
`K = alphaCapacity`, `f = 1/Δ`, `c = 1`.  The absolute normalization is structural.  `alphaCostScale = Δ²/(ν+σ) = 1849/21`
gives the leading collective scale and lands near the U-238 lifetime.  The improved candidate
`alphaCostQ2 = (43/8)Z/√Q − 84` puts most tested alpha emitters within a factor
of four, with U-235 the clear outlier.  The remaining task is deriving this cost
from the collective link counting rather than selecting it from the table.
Residual diagnosis (`ALPHA-TESTS.md`) points to a single-particle/spin-parity
hindrance: even-even residuals are small, while U-235 is a strong odd-A outlier.
`AlphaHindrance` now makes the spin-parity input explicit
(`AlphaLevel.ofOrbital`, `spinMismatch`, `parityChange`, `alphaCostHindered`).
The hindrance scale is still supplied.  Actual U-235/Pu-239 E8 orbital assignments
(`2f7/2`, `2d5/2`, `3s1/2`) reproduce the spin-parity units `3` and `7`; no
single scale fits both.  The remaining term is configuration mixing / Nilsson
deformation.  `AlphaConfiguration` now supplies it with E8 parameters
`κ=1/ν`, `μ=χ/σ`, `δ=1/σ` and `hindrance = σ/(|ΔE|+1/χ)`; this fixes U-235
and Pu-239 while leaving even-even entries unchanged.  The mixing form still
needs a first-principles derivation; its E8-normalized form is
`σχ/(χ·gap+1)`, proved in `alphaMixingHindrance_eq`.  `AlphaConfiguration` now
also records the two-level Hamiltonian `alphaTwoLevel` and the scalar resolvent
`alphaMixingResolvent`; the hindrance is `σχ` times that resolvent.  The full non-zero mixing amplitude is now
`alphaMixingV = κμδ = 1/200`; `alphaMixedGap` dresses the gap by
`√(ΔE²+4V²)`, and `alphaMixingHindranceFull_zero` proves the old formula is the
`V=0` limit.  Because `V` is small, the numerical table is unchanged.  `spinDegeneracy` tests the cheaper
alternative `log((2Jp+1)(2Jd+1))`, which is the best single residual feature so
far but still leaves Pu-239 overcorrected.  `alphaBlockingHindrance` adds the
same `log 2` to both odd-A outliers and is insufficient.  The smooth-term list is
exhausted; the remaining term is the actual level/configuration hindrance.  The
existing comparison table still shows Cm/Cf near the frontier working while
U-234/Pu-238 fail, so alpha remains frontier-local.

## 5b. Continuum / standard-physics remnants to convert

The E8-native beta route is `BetaLattice`; these are comparison/legacy pieces:

| module | continuum content | E8 conversion |
| --- | --- | --- |
| `PMElementaryParticles.NeutronRate` | continuum massive-electron phase space, `G_F`, `g_A` | finite spectral beta rate |
| `PMAtoms.BetaDecay` | continuum beta phase-space integral, Fermi function | finite spectral beta rate |
| `PMAtoms.FermiFunction` | Coulomb Fermi factor | lattice Coulomb phase / finite channel |
| `PMAtoms.SingleParticle` | Nilsson/Strutinsky shell model | E8 level ladder / finite shell count |
| `PMAtoms.ShapePotential` | Landau collective potential | E8 deformation ledger |
| `PMAtoms.CollectiveE8` | Geiger–Nuttall WKB exponent | finite channel cost |
| `PMElementaryParticles.MuonRate` | continuum contact/phase space | finite lattice spectral channel |
| `PMElementaryParticles.MassiveDaughterSpectrum` | continuum massive-daughter phase space | finite lattice spectral channel |
| `PMElementaryParticles.Widths` | supplied reference width | E8 channel hazard |
| `PMAtoms.Nucleus` | supplied cost in `Persists` | E8 cost ledger |

Converted at the structural level:

- `NeutronRate` → `BetaLattice`
- `BetaDecay` → `BetaLattice`
- `FermiFunction` → lattice channel/threshold bound
- `Widths` → `betaHazardE8` / `betaLatticeLifetime`
- `Nucleus` → `e8Cost` / `e8NuclearCost`

Converted structurally:

- `MuonRate`/`MassiveDaughterSpectrum` → `LeptonLattice`
- `SingleParticle` → `e8ShellLadder`/`e8ShellOccupations`
- `ShapePotential` → `e8DeformationLedger`
- `CollectiveE8` → `CollectiveFinite`

The comparison modules remain for numerical checks; their E8 structural
counterparts now exist.

Do not delete the comparison modules until each E8 replacement has a numerical or
structural counterpart.

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
