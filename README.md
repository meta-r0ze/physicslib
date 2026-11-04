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

1. **What are the implications of this repository?** Explain the central claim in plain English: what is genuinely derived, what is a convention, and what is still a physical model input.
2. **Map the whole thing.** Give me a dependency-ordered map of the eight Lean libraries and `e8p`, and say in one sentence what each one owns.
3. **Trace the numbers.** Follow the chain from "some things persist" to D = 4, Δ = 43, ν = 16, χ = 2, σ = 5, and 137.035999212…. Which steps are Lean theorems, which are postulates, and which are physical identifications?
4. **Why E8?** Walk me through the substrate argument in `src/PMSubstrate/OVERVIEW.md` and the `Research/` alternatives. What is forced, and what is assumed?
5. **What exactly does PM prove about Yang–Mills, and what does it explicitly not prove?** Read `src/PMAction/OVERVIEW.md` and `src/PMAction/REVIEW-AND-NEXT.md`.
6. **How does the muon width and lifetime come out of `PMElementaryParticles`?** Which parts are derived from the contact model, and which are phase-space, coupling, or final-state inputs?
7. **Why does this substrate have three generations of matter?** Separate the proved encoding/representation facts from the physical generation law that is still missing.
8. **Make a constants scorecard.** For α, α_s, G_F, W/Z, Higgs, the VEV, and neutrino masses, list "what Lean checks" vs. "what still needs a physical derivation." Use `src/PMConstants/OVERVIEW.md` and `REVIEW-AND-NEXT.md`.
9. **What is `e8p`, and how does a value travel from a Lean theorem to the CLI?** Trace one value end to end without compiling anything. Start at `tools/e8p/README`, `E8PConstants/Catalog.lean`, and `E8PConstantsProof.lean`.
10. **Audit the "no measured constants are inserted" claim.** Where do measured references live, and how would a reviewer check that they never enter theorem statements? Look at `tools/e8p/E8PConstants/Experimental.lean` and the prediction ledgers.
11. **What is the most falsifiable prediction here, and what observation would rule it out?** Then tell me which part of the proof chain that prediction actually depends on."*
12. **Can you create a new proof that is missing that we can compare to experimental values and contribute back?*

Some more ways to contribute: *"Pick one item in any `REVIEW-AND-NEXT.md` and see if it is solvable simply by depending on existing proofs"*

TODO: improve documentation here in this repo
For now it is probably helpful to also clone the following repositories and place it where the AI can access it as this is my initial English explanations.
https://github.com/meta-r0ze/Persistence-Mechanics
https://github.com/meta-r0ze/PM_Quantum_Vacuum_I
https://github.com/meta-r0ze/PM_Quantum_Vacuum_II
https://github.com/meta-r0ze/PM_Quantum_Vacuum_III
https://github.com/meta-r0ze/PM_Quantum_Vacuum_IV
https://github.com/meta-r0ze/PM_Quantum_Vacuum_V
https://github.com/meta-r0ze/PM_Quantum_Vacuum_VI

The entire purpose of this is to test Persistence Mechanics in this domain so if you find another thing that matches what we see in the universe (or not!) please *make a pull requests for Lean proofs you create that I have not yet filled in.* As you will find there is a *lot* that already matches, but still testing.
