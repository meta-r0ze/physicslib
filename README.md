This repository contains Lean proofs for the Physics application of Persistence Mechanics.

# Overview

Persistence Mechanics describes the basic mechanics for any complex system that persists.  More about persistence mechanics can be found here: https://github.com/meta-r0ze/Persistence-Mechanics 

Given the postulates from Persistence Mechanics that anything that persists has Finiteness, Conservation, and Causality and that the vacuum persists, we test that here.
This output is the E8-Persistence theory, an informational theoretic dual to the standard model. The Lean proofs are as followed, each building only on what comes before it.

 * [Persistence Mechanics](src/PersistenceMechanics): survival/hazard, selection
 * [Substrate](src/PMSubstrate): Applying PM to the vacuum to derive the E8 lattice with its split on D4, clock 43, invariants, etc.
 * [Action](src/PMAction) - Applying PM dynamics on the substrate to get the Lagrangian and General Relativity and gauge/scalar transport; `PMAction/MassGap` proves the mass gap of the distinction substrate
 * [Constants](src/PMConstants) - The properties of substrate partitioning (constants, sectors, running, gauge group factors)
 * [Flavor](src/PMFlavor) - Information transfer across the substrate (flavor mixing, wall spectra, propagation)
 * [Elementary Particles](src/PMElementaryParticles) - Systems that can persist on top of the substrate. (protocols, decay rates)
 * [Hadrons](src/PMHadrons) - Quark composites: nucleons (proton, neutron) with the full six-pillar mass ledger, mesons, and their decays
 * [Atoms](src/PMAtoms) - Further recursive systems: nucleus (the shape is sort of like chemistry), shell, atom (ending with the full periodic table list of particles that can persist)
 * [Cosmology](src/PMCosmology) - The lifetime of the substrate systems (expansion of the universe equations, etc)
 * [e8p](tools/e8p) command line tool to output the lean values you can compare against experimental physics values.

Todo: need to write a better overview, but as a placeholder here is my blog entry from April 2026 which walks through most of it at a high level.
https://metamagic.substack.com/p/persistence-mechanics-and-the-quantum-vacuum

The goal of the Lean proofs is to only assume that some things persist without inserting anything from the Standard Model, known physics equations or constants, nor is any hand tuned values inserted.

# Use your AI to explore

Knowing that everyone is using AI, without compiling anything you can still point your AI at this repo and ask fun questions like:

 * Does this cross the "too many coincidences and requires further investigation" line?
 * Give me an overview of how the systems stack from persistence through the E8 system followed by elementary particles, hadrons, nucleus, shell, and atoms
 * Give me a dependency-ordered map of the Lean libraries and `e8p`, and say in one sentence what each one owns.
 * Why E8? Walk me through the substrate argument in `src/PMSubstrate/OVERVIEW.md` and the `Research/` alternatives. What is forced, and what is assumed?
 * Why does this substrate have three generations of matter?
 * How does the muon width and lifetime come out of `PMElementaryParticles`?
 * Can this make falsifiable prediction, how many?
 * Can you create a new proof that is missing that we can compare to experimental values and contribute back?

# Documentation map

Each module under `src/` has three documents with separate jobs:

```text
README.md           build, layout and import boundary
OVERVIEW.md         what is checked, with theorem entry points
REVIEW-AND-NEXT.md  what remains open or is a model input
```

The Lean source is the ground truth.  Notes that are only comparison data or
validation tables live with the module they describe; they are not theorem inputs.
The cross-cutting map of open physics questions — where the papers discuss them and
whether the tree covers them — is [`SCOPE.md`](SCOPE.md); the premises,
inputs and open physics a reader should know about are in
[`OPEN-PROBLEMS.md`](OPEN-PROBLEMS.md); each folder's `REVIEW-AND-NEXT.md` has the working list.
How a lattice gives continuum results, and when it does not, is explained in
[`src/PMElementaryParticles/CONTINUOUS.md`](src/PMElementaryParticles/CONTINUOUS.md).

For more English background, it is helpful to clone the following older draft repositories and place them where the AI can access them.
https://github.com/meta-r0ze/Persistence-Mechanics
https://github.com/meta-r0ze/PM_Quantum_Vacuum_I
https://github.com/meta-r0ze/PM_Quantum_Vacuum_II
https://github.com/meta-r0ze/PM_Quantum_Vacuum_III
https://github.com/meta-r0ze/PM_Quantum_Vacuum_IV
https://github.com/meta-r0ze/PM_Quantum_Vacuum_V
https://github.com/meta-r0ze/PM_Quantum_Vacuum_VI

The entire purpose of this is to test Persistence Mechanics in this domain so if you find another thing that matches what we see in the universe (or not!) please *make a pull requests for Lean proofs you create that I have not yet filled in.* As you will find there is a *lot* that already matches, but still testing.
