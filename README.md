This repository contains Lean proofs for the Physics application of Persistence Mechanics.

# Overview

Persistence Mechanics describes the basic mechanics for any complex system that persists.  More about persistence mechanics can be found here: https://github.com/meta-r0ze/Persistence-Mechanics 

Given the postulates from Persistence Mechanics that anything that persists has Finiteness, Conservation, and Causality and that the vacuum persists, we test that here.
This output is an informational theoretic dual to the standard model. The Lean proofs are as followed, each building only on what comes before it.

 * [Persistence Mechanics](src/PersistenceMechanics): survival/hazard, selection
 * [Substrate](src/PMSubstrate): Applying PM to the vacuum to derive the E8 lattice with its split on D4, clock 43, invariants, etc.
 * [Action](src/PMAction) - Applying PM dynamics on the substrate to get the Lagrangian and General Relativity and gauge/scalar transport; `PMAction/MassGap` proves the mass gap of the distinction substrate
 * [Constants](src/PMConstants) - The properties of substrate partitioning (constants, sectors, running, gauge group factors)
 * [KAutomaton](src/PMKAutomaton) - Reversible carrier, reference, and record transfer between E8 nodes.
 * [Elementary Particles](src/PMElementaryParticles) - Systems that can persist on top of the substrate. (protocols, decay rates)
 * [Flavor](src/PMFlavor) - Information transfer (flavor mixing, wall spectra, propagation)
 * [Hadrons](src/PMHadrons) - Quark composites: nucleons (proton, neutron) with the full six-pillar mass ledger, mesons, and their decays
 * [Atoms](src/PMAtoms) - Further recursive systems: nucleus (the shape is sort of like chemistry), shell, atom (ending with the full periodic table list of particles that can persist)
 * [Cosmology](src/PMCosmology) - The lifetime of the substrate systems (expansion of the universe equations, etc)

Todo: need to write a better overview, but as a placeholder here is my blog entry from April 2026 which walks through the layers at a high level.
https://metamagic.substack.com/p/persistence-mechanics-and-the-quantum-vacuum

The Lean proofs are conversions and the goal is to only assume that some things persist without inserting anything from the Standard Model, known physics equations or constants.


# Results

tools/e8p can output all or any specific lean values and the matching experimental value.

The full list can be seen here: [e8p.txt](tools/e8p/e8p_output.txt)

Example:
- **1836.152673444–1836.152673445** The Lean proton/electron mass ratio
- **1836.152673426 ± 0.000000032** The experimental reference 

Every value has a Lean proof chain that can be outputed:

```sh
./build.sh e8p
./.lake/build/bin/e8p --only=proton_ratio
./.lake/build/bin/e8p --derivation proton_ratio --depth 2
```

## Audit
e8p can also generate audits for some or all of the results with --audit

| Selection | Scored comparisons | χ² | Reduced χ² |
|---|---:|---:|---:|
| Constants | 7 | 2.031 | 0.290 |

## Atoms

The lean proofs go from quantum mechanics to classical mechanics and so you can output information about atoms (no mass gap btw).

- `e8p --shells` prints the nuclear shell closures
- `e8p --masses=6,6` outputs the carbon-12 mass ledger
- `e8p --periodic-table` outputs the persistent atomic configurations.


# Explore using your AI

You can point your AI at this repo without compiling the Lean and ask questions like:

 * Does this cross the "too many coincidences and requires further investigation" line?
 * Give me an overview of how the systems stack from persistence through the E8 system followed by elementary particles, hadrons, nucleus, shell, and atoms
 * Give me a dependency-ordered map of the Lean libraries and `e8p`, and say in one sentence what each one owns.
 * Why E8? Walk me through the substrate argument in `src/PMSubstrate/OVERVIEW.md` and the `Research/` alternatives. What is forced, and what is assumed?
 * Why does this substrate have three generations of matter?
 * How does the muon width and lifetime come out of `PMElementaryParticles`?
 * Can this make falsifiable prediction, how many?
 * Can you create a new proof to contribute back?

# Documentation map

Each module under `src/` has three documents with separate jobs:

```text
README.md           build, layout and import boundary
OVERVIEW.md         what is checked, with theorem entry points
REVIEW-AND-NEXT.md  what remains open from the paper conversion
```
How a lattice gives continuum results, and when it does not, is explained in
[`src/PMElementaryParticles/CONTINUOUS.md`](src/PMElementaryParticles/CONTINUOUS.md).

For a more English background, it is helpful to clone the following older draft repositories and place them where the AI can access them.
https://github.com/meta-r0ze/Persistence-Mechanics
https://github.com/meta-r0ze/PM_Quantum_Vacuum_I
https://github.com/meta-r0ze/PM_Quantum_Vacuum_II
https://github.com/meta-r0ze/PM_Quantum_Vacuum_III
https://github.com/meta-r0ze/PM_Quantum_Vacuum_IV
https://github.com/meta-r0ze/PM_Quantum_Vacuum_V
https://github.com/meta-r0ze/PM_Quantum_Vacuum_VI
