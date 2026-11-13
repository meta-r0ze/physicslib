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

## Step 2: values (Nov 2026, first pass)

**Margin** (energy distance to the nearest cheaper state with the same charges; E8 masses):

| system | nearest cheaper state | Margin |
|---|---|---|
| proton | none | stable |
| neutron | `p e ν̄` (weak) | `+0.782 MeV` (`m_n − m_p − m_e`) |
| `π±` | `μ ν` (weak) | `+33.9 MeV` |
| Δ | `N π` (strong) | `−154 MeV` (observed Δ; no E8 Δ) |
| virtual pion | — | `−m_π` for `ħ/m_π` |

The persistent systems have positive Margin and decay only through Toll (weak); the Δ and the
virtual pion have negative Margin and are hosted transients.

**Protocol** (exchange between the carriers; sets N–Δ and dresses `g_A`). Two exchanges, both
computed without fitting (`tools/pion_cloud_cube.py`, `tools/colour_fluctuation.py`):

* pion exchange, source confined: `Δ − N = 79 MeV`, `δg_A/g_A = −7.6%`;
* colour exchange at the coupling the running reaches at the cube (`α_V ≈ 1.3`, one loop in the
  static-potential scheme, `tools/cube_coupling_running.py`): `Δ − N ≈ 131 MeV`,
  `δg_A/g_A ≈ −0.8%`.

**The two Toll readings, side by side:**

| Toll reading | `g_A` (bare `1.377`) | `Δ − N` | comparison |
|---|---|---|---|
| (a) a returning pair is one Protocol exchange; Toll weights only irreversible boundary events | `≈ 1.26` | `≈ 210 MeV` | lattice `1.246(28)`; observed `293` |
| (b) every boundary crossing pays `tollTerm` | `≈ 1.37` | `≈ 131 MeV` | |

Reading (a) lands `g_A` on the lattice value and gives `72%` of the splitting with no calibration;
(b) leaves both where the bare cube is. The colour coupling here is the perturbative one-loop value,
the least reliable input.

**Governor** (bound on feedback). The running coupling grows without bound just above the cube
scale (two-loop pole near `400 MeV`). A Governor at the hadron level would cap that growth. The
value the one-loop running reaches at the cube, `α_V ≈ 1.3`, is used above; whether Governor
fixes the cap there, and with what E8 number, is open.

**Capacity** (intake covers consumption). The cube's refreshed room is 27 sites and the ground
cohort is 20 spin–flavour states; the nucleon base is Margin's cone `Δ²` (proved). A Capacity
value for the nucleon that is not one of these counts has not been identified.

**Magnetic null test, reading (a)** (`tools/pion_cloud_cube.py`, source-confined cloud; core
moment from `tools/proton_moment.py`, dressed like `g_A`; pion current `e m/(2ω)` per p-wave
charged pion):

| core current | N–Δ in denominators | `μ_p` (cloud) | `μ_n` (cloud) | `P_π` | `μ_n + (2/3)μ_p` |
|---|---|---|---|---|---|
| on-site | 0 | `1.88` (`+0.25`) | `−1.35` (`−0.25`) | `0.42` | `−0.097` |
| on-site | 293 MeV | `1.79` (`+0.21`) | `−1.31` (`−0.21`) | `0.27` | `−0.123` |
| link | 293 MeV | `1.15` (`+0.21`) | `−0.87` (`−0.21`) | `0.27` | `−0.102` |
| measured | | `2.793` | `−1.913` | | `−0.051` |

Reading (b) gives `0` for the null combination. The measured `−0.051` lies between: (a) has the
right sign and about twice the size. The cloud is close to isovector (`δμ_n ≈ −δμ_p`), as
expected, and adds only `0.2` to `μ_p`; the proton's moment stays low by `1.0` under both
readings, so the core moment itself (the carrier's spatial extent) is the larger issue there.
The Toll question is therefore not settled by this test: `g_A` favours (a) at full size, the null
test favours a cloud about half as large.

**The scale (Nov 2026).** The spacing `a` was fixed by setting the carrier's rms radius, measured
from the cube centre, equal to `r_p`. Experiment measures the charge radius relative to the
nucleon's centre of mass, and for three carriers in independent identical modes
`⟨(r_i − R_cm)²⟩ = (2/3)⟨r²⟩`. So `r_p² = (2/3)ρ²a²`, `a = 0.761 fm`, `1/a = 259 MeV` (was
`0.621 fm`, `318 MeV`). This is a correction of the reading, not a fit. With it (reading (a),
source-confined cloud, on-site core):

| quantity | `1/a = 318` | `1/a = 259` (CM radius) | measured / target |
|---|---|---|---|
| `μ_p` | `1.79` | `2.15` | `2.793` |
| `μ_n + (2/3)μ_p` | `−0.123` | `−0.089` | `−0.051` |
| cloud `δg_A/g_A` | `−7.6%` | `−4.8%` | `−9.2%` to `5/4` |
| cloud `Δ − N` | `79 MeV` | `41 MeV` | (part of `293`) |

(with the physical splitting in the denominators). The CM-relative radius moves `μ_p` and the null
test toward the data and `g_A` away from it. Not yet included: the centre-of-mass corrections to
`μ` and `g_A` themselves (a projected, translation-invariant nucleon state), which in bag models
change both by tens of percent. That is the next consistent step; without it the three
observables cannot be weighed against each other.

## Next

* Discriminate the Toll readings with the magnetic null test `μ_n + (2/3)μ_p` (measured
  `−0.051` n.m.): (b) gives `0` (no cloud); (a) shifts it by the cloud's isovector and isoscalar
  moments, which needs the pion current added to `tools/pion_cloud_cube.py`.
* Governor: an E8 statement for the cap on the colour coupling at the cube scale.
* Step 3: compare with the mass ledgers (`CompositeMasses`, `MesonMasses`).
