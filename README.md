This repository contains Lean proofs for the Physics application of Persistence Mechanics.

The proofs are grouped based on their area:

 * Persistence Mechanics: survival/hazard, selection
 * Substrate: Applying PM to the vacuum to derive the E8 lattice with its split on D4, clock 43, invariants, etc.
 * Action - Applying PM dynamics on the substrate to get the Lagrangian and General Relativity and gauge/scalar transport
 * Constants - The properties of substrate partitioning (constants, sectors, running, gauge group factors)
 * Flavor - Information transfer across the substrate (flavor mixing, wall spectra, propagation)
 * Elementary Particles - Systems that can persist on top of the substrate. (protocols, decay rates)
 * Atoms - Further recursive systems: nucleon (proton, neutron), nucleus (the shape is sort of like chemistry), shell, atom (ending with the full periodic table list of particles that can persist)
 * Cosmology - The lifetime of the substrate systems (expansion of the universe equations, etc)
 * e8p command line tool to output the lean values you can compare against experimental physics values.

The goal of the Lean proofs is to only assume that some things persist. No known physics equations or constants (other than say electron mass to convert to known values) are used, nor is any hand tuned values inserted.  The Lean proofs (should) only contain values derived from prior proofs. The Standard Model logic should be derived, not inserted.

# Overview

Persistence Mechanics is the basic mechanics for any complex system that persists.  Given the postulates from Persistence Mechanics that anything that persists has Finiteness, Conservation, and Causality and that the vacuum persists, we test this by translating it to geometry and seeing what happens. This output is the E8-Persistence theory, an informational theoretic dual to the standard model.  More about persistence mechanics can be found here: https://github.com/meta-r0ze/Persistence-Mechanics and further testing it in other domains such as biology or software engineering can be found on https://metamagic.substack.com

This application forces a single substrate, E8, with its characteristic values D = 4, Δ = 43 ν = 16, χ = 2, and σ = 5. And the index value, read as net transitions per cycle has the value 137.035999212…

Todo: need to write a better version, but as a placeholder here is my blog entry from April 2026 which walks through most of it at a high level.
https://metamagic.substack.com/p/persistence-mechanics-and-the-quantum-vacuum

# Use your AI to explore and contribute!

You do not need to compile anything to start. Point your AI at this repo and then ask:

 * Does this cross the "too many coincidences and requires further investigation" line?
 * Give me an overview of how the systems stack from persistence through the E8 system followed by elementary particles, nucleons, nucleus, shell, and atoms
 * Give me a dependency-ordered map of the eight Lean libraries and `e8p`, and say in one sentence what each one owns.
 * Why E8? Walk me through the substrate argument in `src/PMSubstrate/OVERVIEW.md` and the `Research/` alternatives. What is forced, and what is assumed?
 * What exactly does PM prove about Yang–Mills, and what does it explicitly not prove? (See PMAction)
 * How does the muon width and lifetime come out of `PMElementaryParticles`?
 * Why does this substrate have three generations of matter?
 * Can this make falsifiable prediction, how many?
 * Can you create a new proof that is missing that we can compare to experimental values and contribute back?

Some more ways to contribute: *"Pick one item in any `REVIEW-AND-NEXT.md` and see if it is solvable simply by depending on existing proofs"*

# Documentation map

Each module under `src/` has three documents with separate jobs:

```text
README.md           build, layout and import boundary
OVERVIEW.md         what is checked, with theorem entry points
REVIEW-AND-NEXT.md  what remains open or is a model input
```

The Lean source is the ground truth.  Notes that are only comparison data or
validation tables live with the module they describe; they are not theorem inputs.

For more English background, it is helpful to clone the following repositories and place them where the AI can access them.
https://github.com/meta-r0ze/Persistence-Mechanics
https://github.com/meta-r0ze/PM_Quantum_Vacuum_I
https://github.com/meta-r0ze/PM_Quantum_Vacuum_II
https://github.com/meta-r0ze/PM_Quantum_Vacuum_III
https://github.com/meta-r0ze/PM_Quantum_Vacuum_IV
https://github.com/meta-r0ze/PM_Quantum_Vacuum_V
https://github.com/meta-r0ze/PM_Quantum_Vacuum_VI

The entire purpose of this is to test Persistence Mechanics in this domain so if you find another thing that matches what we see in the universe (or not!) please *make a pull requests for Lean proofs you create that I have not yet filled in.* As you will find there is a *lot* that already matches, but still testing.
