This repository contains Lean proofs for the Physics application of Persistence Mechanics.

# Overview

Persistence Mechanics describes the basic mechanics for any complex system that persists.  More about persistence mechanics can be found here: https://github.com/meta-r0ze/Persistence-Mechanics 

Given the postulates from Persistence Mechanics that anything that persists has Finiteness, Conservation, and Causality and that the vacuum persists, we test that here.
This output is an informational theoretic dual to the standard model. The Lean proofs are as followed, each building only on what comes before it.

 * [Persistence Mechanics](src/PersistenceMechanics): survival/hazard, selection
 * [Substrate](src/PMSubstrate): Applying PM to the vacuum to derive the E8 lattice with its split on D4, clock 43, invariants, etc.
 * [Action](src/PMAction) - Applying PM dynamics on the substrate to get the Lagrangian and General Relativity and gauge/scalar transport; `PMAction/MassGap` proves the mass gap of the distinction substrate
 * [Constants](src/PMConstants) - The properties of substrate partitioning (constants, sectors, running, gauge group factors)
 * [Elementary Particles](src/PMElementaryParticles) - Systems that can persist on top of the substrate. (protocols, decay rates)
 * [Flavor](src/PMFlavor) - Information transfer (flavor mixing, wall spectra, propagation)
 * [Hadrons](src/PMHadrons) - Quark composites: nucleons (proton, neutron) with the full six-pillar mass ledger, mesons, and their decays
 * [Atoms](src/PMAtoms) - Further recursive systems: nucleus (the shape is sort of like chemistry), shell, atom (ending with the full periodic table list of particles that can persist)
 * [Cosmology](src/PMCosmology) - The lifetime of the substrate systems (expansion of the universe equations, etc)

Todo: need to write a better overview, but as a placeholder here is my blog entry from April 2026 which walks through the layers at a high level.
https://metamagic.substack.com/p/persistence-mechanics-and-the-quantum-vacuum

The Lean proofs are conversions and the goal is to only assume that some things persist without inserting anything from the Standard Model, known physics equations or constants.

# E8p - Experimental comparisons

* [e8p](tools/e8p) is a command line tool to output the lean values against experimental physics values.

After building with `./build e8p` you can run `./.lake/build/bin/e8p --help` to output values. 

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
