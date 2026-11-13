# The six pillars at the hadron level

Each persistent system has its own six pillars (`PMAtoms/SystemTower`). `PMAtoms/ShellSystem`
showed the method: say what each pillar **does** in that system, then compute the system's value.
This file does step 1 of that for the hadrons: the roles, with where each comes from. Values
(step 2) and the comparison with the mass ledgers, `g_A` and N–Δ (step 3) come after, so the
roles are not tuned to the numbers.

## Sources for the roles

* **Mechanism of each pillar** (`PMSubstrate/Pillars`): Capacity = intake covers consumption;
  Margin = distance to the non-viable set; Map = correction toward a retained reference;
  Protocol = exchange between components keeps them coherent; Toll = a positive minimum cost per
  transition; Governor = a bound on feedback.
* **Shell level** (`PMAtoms/ShellSystem`): Capacity = the `2n+l` room; Map = the closure
  boundary (`χ`); Protocol = the ordering; Governor = the level spacing; Toll = emission;
  Margin = the reference cone.
* **Composite level, already in the library:** Map base `χ` cells and Protocol's `σ` direction
  register for mesons (`MesonMasses`, `StrangeCarrier`); Margin's causal cone `Δ²` as the
  nucleon base (`NucleonBase`, proved); Toll = the emission boundary with weight `tollTerm` and
  Governor = per-slot persistence `χ/Δ` (`TollGovernor`).
* **The carrier cube** (`PMAction` REVIEW A, Nov 2026): hard wall (no link out), three carriers in
  one ground orbital, `Sym³(4) = N (4) + Δ (16)` at `3E₀`, colour singlet.

## Roles

| Pillar | Mechanism | Nucleon (the cube) | Δ | Pion (persistent, `π±`) | Virtual pion (in the cloud) |
|---|---|---|---|---|---|
| **Capacity** | intake covers consumption | the cube's refreshed room: 27 sites, the 20-state ground cohort | same room as N | `χ = 2` cells (`pion*_cells`) | none of its own: it draws on the host |
| **Map** | correction toward a retained reference | the colour-singlet reference (`ColourSinglet`) held inside the wall; the wall is where it is kept | same | its own pair singlet | its own pair singlet — **not** the host's closure |
| **Protocol** | exchange keeps components coherent | exchange between the three carriers (colour; pions) that keeps the symmetric spin–flavour state; the `5/3` count is its ordering (`AxialCount`) | same exchange, other spin–flavour state | quark–antiquark exchange | the exchange itself (one Protocol event between host carriers) |
| **Toll** | positive minimum cost per transition | boundary transition = emission (`TollGovernor`, weight `tollTerm`) | — | its weak decay (Toll boundary) | **open:** does a pion that leaves and re-enters the host pay Toll? |
| **Governor** | bound on feedback | per-slot persistence `χ/Δ`; candidate: the cap on the colour coupling's growth at the cube scale | — | per-slot `χ/Δ` | — |
| **Margin** | distance to the non-viable set | the causal cone `Δ²` (base, proved); positive energy margin (no cheaper state with its charges) | **negative**: `N + π` lies `153 MeV` below it, so it is not persistent | positive (lightest hadron) | negative for its lifetime: it borrows `m_π` for `ħ/m_π` |

## What the roles already say

1. **Which pillar fails for the Δ: Margin.** It has a cheaper configuration with the same
   charges (`N + π`), so its distance to the non-viable set is negative. That is why it has no
   occupancy mass, and it is a level of the cube, not a persistent system.
2. **The pion boundary question is a Map question.** Map holds the host's retained reference, the
   colour singlet, inside the wall. A colour-singlet pion carries its own reference, so the host's
   Map does not bound it: the host confines the pion's **source**, not its field. This follows from
   Map's role as defined above, before the `g_A` numbers.
3. **But Toll raises a tension.** If the pion leaves the host volume and comes back, it crosses the
   boundary twice. If every crossing is a Toll event with weight `tollTerm ≈ 1.2×10⁻⁵`, the cloud
   would be negligible. Either Toll's weight applies only to shedding a carrier for good (a decay),
   not to a pair that returns, or the cloud is suppressed. The roles do not settle this yet.
4. **N–Δ is a Protocol value.** The splitting is the cost difference between two spin–flavour
   states kept coherent by inter-carrier exchange. In the shell system the spacing was Governor's;
   here the competing states are distinguished by the exchange, so Protocol is the candidate.

## Next

* Step 2: values per system — the cube's Capacity room, the Protocol exchange cost (N–Δ), the
  Governor cap (colour coupling), and the Toll rule for a returning pair.
* Step 3: compare with the mass ledgers (`CompositeMasses`, `MesonMasses`), `g_A`, N–Δ.
