# PMAtoms checkpoint

## Certified core

- `NuclearLedger.certifiedMass` on `certifiedDomain = deformedFrontier`
- nuclear Q-values and regime-aware decay selection
- exit table: `β⁻`, `β⁺`, `α`, fission
- `e8NuclearCost` persistence ledger

## E8 decay chains

### Beta

```
finite spectral channel
hazard G_F²/(σ−χ)
margin = surviving phase fraction after χ gap = 41/43
τ_n ≈ 877.2 s vs 878 s
```

### Alpha

```
smooth cost: (43/8)Z/√Q − 84
odd-A two-level mixing: σχ/(χ·ΔE + 1)
```

U-235 and Pu-239 are fixed without disturbing the even-even chain.

### Fission

```
fissility: 1849/27 − 10(Z²/A − 39)
Sn-132 shell gain: 43/6
Coulomb/Δ
superheavy governor: χ·max(Z−100,0)
light-fragment yield: exp(−d_light/6)
measure scale: Δ²/(D+σ) = 1849/9
```

The five-nucleus set is within a factor of ~1.6:

```
U-238, Cf-252, Fm-254, No-252, Rf-256
```

## Known limitations

- beta spectral fraction is an external numerical comparison
- `41/43` margin and alpha mixing are candidate E8 forms
- fission out-of-sample U-234/Pu-242 fixed by E8 subshell costs at N=142/148
- full fragment-yield measure and superheavy data remain open

## Non-E8 comparison modules

`NeutronRate`, `BetaDecay`, `FermiFunction`, `MuonRate`,
`MassiveDaughterSpectrum`, `Widths`, `SingleParticle`, `ShapePotential`,
`CollectiveE8` remain comparison/legacy pieces with E8 structural counterparts.

## Build

```
PMAtoms: 4349 jobs
```

## Shared decay wiring

```
PersistenceMechanics.DecayChannel      six-pillar rate template
PersistenceMechanics.ChannelMeasure    finite normalized channel measure
PersistenceMechanics.MarginCorrection  supplied margin correction
PMSubstrate.E8Margin                   phase margin 41/43
```

Carrier bridge:

```
CarrierSpecies → charge/mass
CarrierAmplitude → em/weak/strong slots
CarrierTransition → transition amplitude ledger
```

E8 clock:

```
e8Tick = Δ = 43
e8TickSeconds = Δ · electronSecond
```

These are structural wiring layers.  They do not change existing numerical
predictions.

## Next

1. Connect `CarrierAmplitude` to the actual `PMAction` transition operator.
2. Derive the physical mode-selection rule from the spectral cutoff.
3. Fix the numerical E8 tick conversion.
4. Apply `E8Margin`/`MarginCorrection` only after 1–3.
