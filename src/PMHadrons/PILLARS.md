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
   occupancy mass, and it is a level of the cube, not a persistent system. **Scope decision
   (Nov 2026):** this library is a study of what persists. Resonances such as the Δ (and the
   virtual pion) are documented as hosted transients: they exist, decay, and depend on their host
   and environment; their masses and widths are not targets here.
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

**Centre-of-mass projection of `g_A`** (`tools/cm_projection.py`, Peierls–Yoccoz on the lattice:
the product state summed over translations of the whole system to zero total momentum). It
**raises** the cube's axial charge: `⟨Σ_z⟩ 0.826 → 0.895` (`+8.4%`), `g_A 1.377 → 1.492` on `3³`
(`1.265 → 1.426` on `4³`). Removing the spurious centre-of-mass motion lowers the carriers'
relative momenta, so they are less relativistic. Combined with the cloud at the CM-relative scale
(`−4.8%`), `g_A ≈ 1.42`, `14%` above `5/4`. So the translation-invariant cube is further from
`g_A` than the bare one; the cloud alone (at its computed size) does not close it.

The same projection for the magnetic moment needs the intrinsic current (velocities relative to
the centre of mass and the recoil term); a first attempt with positions alone was not consistent
and is not recorded. Bag-model studies find that the centre-of-mass correction raises `μ`.

**Sites or cells? (Nov 2026)** The minimal cube's 3 per edge can be read as substrate *sites*
(the carrier lives on a 3-point lattice; everything above) or as persistence *cells* (each cell
holds many substrate sites, and the carrier is resolved on the finer substrate inside a 3-cell
volume). A structural argument, made before the numbers below: `CubeScales.two_units` proves the
carrier cube and the lepton cube cannot share one spacing, and each system has "its own minimal
cube at its own scale". A per-system spacing cannot be the substrate's fundamental spacing for
both, so at least one cube is a cube of cells; the cells reading is the consistent one.

Refining the lattice inside the same box (`tools/cm_projection.py`):

| sites per edge | `g_A` bare | `g_A` CM-projected |
|---|---|---|
| 3 (sites reading) | `1.377` | `1.492` |
| 6 | `1.153` | `1.361` |
| 9 (toward the cells reading) | `1.105` | `1.344` |

The bare value tends to the bag's `1.09`; centre-of-mass projection raises it to about `1.34`. With
the source-confined cloud at the size computed above (`−4.8%` to `−7.6%`; to be recomputed with
the fine carrier as its source), the cells reading gives `g_A ≈ 1.24–1.28`, on lattice QCD's
`1.246(28)`; the sites reading gives `≈ 1.42`. This is the standard bag + CM + cloud structure,
here with no fitted parameter. Next: the cloud and the magnetic moments with the fine carrier.

## The meson system (step 1 for `f_π`, `f_K`; Nov 2026)

Roles first, from the mechanisms and the library, before counting:

| Pillar | Pion (`u d̄`, two point carriers) | Kaon (`u s̄`, one line carrier) |
|---|---|---|
| Capacity (room) | `χ = 2` cells (`pionPlus_cells`) | `χ + σ = 7` cells (`kaonPlus_cells`) |
| Map (retained reference) | the pair's colour singlet; two-sided closure `χ` | same |
| Protocol (exchange keeps components coherent) | two point carriers: nothing to keep aligned beyond the pair | the line carrier's `σ`-direction register must stay coherent with its partner (`StrangeCarrier`) |
| Toll (cost per transition) | emission boundary: `χ` leg orientations × `R_M − σ = 167` targets (`TollGovernor`) | same boundary, plus the register's own `σ` addresses held |
| Governor (feedback bound) | per-slot `χ/Δ`; `Δ − χ = 41` surviving phases | same |
| Margin (distance to non-viable; cone) | one-cycle cone `Δ²`; Margin to `μν` `+33.9 MeV` | same cone; Margin to `μν` `+388 MeV` |

`|Ω_π| = Δ² + (Δ − χ) = 1890` is Margin's cone plus Governor's survivors (`EmissionSpace`). The
table says the kaon differs only in Capacity (room) and Protocol (the register), so its emission
set must differ through those. The target is `|Ω_K| ≈ 1581–1586`, about `306` fewer modes.

**Where it stands.** The Protocol mechanism says *that* the register must be kept coherent while
the pair annihilates, but not *how many* emission events that removes: the answer depends on
whether the register restricts events of the cone (a spatial cut), phases of the cycle (a
Governor-like cut), or targets (a Toll cut, which acts on the rate, not on `f`). Each choice is a
further premise. Counting all three and keeping the one that lands in the window would be a fit,
so this is recorded as the open premise: **what does keeping a direction register coherent cost a
pair at the moment it annihilates?** The pillar view also shows why the earlier rules failed:
they cut the cone (Margin) or the survivors (Governor), the two pillars the kaon shares with the
pion.

**What `PMAction/Machine` says about the register (Nov 2026).** `IndependentRegisters` builds an
internal label as a separate occupied register bank: the configuration is a product, relabelling
one bank leaves the other untouched (`left_untouched`, `right_untouched`), the two updates
commute (`updates_commute`), and the readout is the tensor product (`tensor_observed`).
`RegisterReference` shows the carrier's chiral-charge evolution and the record routing commute at
the readout (`charge_observed`, `route_observed`). If the kaon's direction register is such a
bank, keeping it coherent costs nothing at the emission readout: Protocol removes **no** emission
modes, `|Ω_K| = |Ω_π|` from counting, and `f_K = f_π`, against the measured `1.19`. So, given that
reading, the `f_K` difference is not a register effect in the emission count; it has to come from
what the count leaves out. The count `f = v/|Ω|` contains no carrier mass, while in QCD
`f_K/f_π − 1` is driven by the strange mass. The kaon's Margin to `μν` (`388 MeV` vs `34 MeV`)
is the pillar value that carries that mass, and it is the next place to look. `WalkSpeed` (a
massive species is slower, `|cos r|`) is the other mass channel; a slower cone was tried
(`REVIEW-AND-NEXT` §3) and needs a persistence-fixed speed.

**What E8 itself says (Nov 2026).** E8's assigned kaon count is `|Ω_K| = Δ² − ν² = 1593`
(`EmissionScale.kaonModes`): the one-cycle cone with its first `ν` time slices removed, and no
Governor survivors. In pillar terms this has a reading that combines the two `Machine` facts: the
register's routing costs nothing at the readout (`RegisterReference`), but every transition costs
at least one tick (Toll, `Pillars.toll_excludes_zeno`). If the line carrier's register is routed
through the `ν = 16` chiral channels of its sector (`Channels`: `ν` per sector) one transition per
tick before the pair can annihilate, the kaon's emission cone starts `ν` ticks late:
`Σ_{t=ν}^{Δ−1}(2t+1) = Δ² − ν²`. So Protocol's cost is paid in Toll time, not in amplitude. Two
things are not explained: why routing takes all `ν` channels, and why the kaon keeps none of the
`Δ − χ` survivors the pion keeps (with them, `1634`, ratio `1.157`). As assigned, `f_K/f_π =
1890/1593 = 1.1864` against FLAG `1.1934(19)`: `0.6%` low. A persistence reading of the second point: the
survivors are the boundary phases at the end of the cycle through which the pion leaves
(`EmissionSpace.survivingPhases`); the kaon's register routing starts at the cycle boundary, so
those exits are occupied by the next cycle's routing and the kaon keeps none. This gives a
mechanism for E8's whole count, but it was found by asking what reproduces `Δ² − ν²`, so it
explains the assigned number rather than predicting a new one, and the `0.6%` stays open.

## Next

* The Toll question (a)/(b) for a returning pion pair: the magnetic null test (done, above)
  favours a cloud about half the size `g_A` favours; it needs a substrate rule, not another test.
* Governor: an E8 statement for the cap on the colour coupling at the cube scale.
* Step 3: compare with the mass ledgers (`CompositeMasses`, `MesonMasses`).

## Appendix: calculation log (moved from `PMAction/REVIEW-AND-NEXT.md` A.3, Nov 2026)

Kept for the record, in the order it happened; later entries correct earlier ones (the `5.6`/`1.27` exchange result, the `4³` candidate and the `Z_A = 1` claim are all superseded as noted).

**The colour coupling on the carrier cube (open, Nov 2026).** `tools/colour_fluctuation.py`
computes one-gluon exchange among the three confined carriers (ground mode, singlet factor
`−2/3`, `CubeGreen3` propagator). With the ledger coupling `α_s = 0.118` on the cube, the
`g_A` correction is `−0.16%` and the N–Δ splitting is `6 MeV` (observed `293 MeV`). So the
argument "the same dimensionless lattice coupling on every persistent cube" is contradicted by
the N–Δ splitting: the observed splitting needs an effective `α_s ≈ 5.6` on the carrier cube.
Both effects are linear in the coupling, so their ratio is coupling-free: calibrated by the
observed `293 MeV`, first-order exchange gives `g_A ≈ 1.27` (measured `1.2754`), i.e. the `+8%`
is the same hyperfine physics that splits N and Δ. Caveats: first order at a large coupling,
positive-energy modes only, static propagator.

**Running to the cube (Nov 2026, `tools/cube_coupling_running.py`).** Persistence says where
the coupling is read: colour is read at the executing mass (`PMConstants.ReadScale`), so the
carrier cube reads it at `1/a = 318 MeV`, not at the Z. Every input to the running is already
in the library: `α_s(m_Z)`, the derived one-loop `b₀ = 11N/3 − 2n_f/3`
(`RunningCoefficients.b0`), and the thresholds at the E8 masses `m_c = 1267 MeV`,
`m_b = 4182 MeV` (`PMConstants.StrongRunning`). One loop gives `α_s(1/a) = 0.87`, with
`Λ₃ = 142 MeV`, so `1/a ≈ 2.2 Λ₃`. Two loops (continuum `b₁`, as a stability test) reach a
pole near `400 MeV`, above `1/a`. So the scale is now fixed by persistence, but the value is
not: the carrier cube sits in the non-perturbative region, where running does not determine
the coupling. The needed effective `5.6` is above the one-loop `0.87`, as it should be there,
but nothing yet derives it. Open: a non-perturbative colour computation on the `3³` cube itself
(for example the static potential from Wilson loops at the cube's own coupling). No E8 value
for the Δ mass exists yet, so the N–Δ calibration stays a comparison.

**Target corrected (Nov 2026).** The carrier computation gives the strong-interaction axial
charge, so its target is lattice QCD's `1.246(28)`, not the measured `1.2754`, which carries a
`1.4–2.6%` electromagnetic correction (PMHadrons REVIEW §0). E8's `5/4` sits on the lattice
value.

**Boundary condition for the colour field (Nov 2026) — retracts the `1.27` above.** The
exchange above used the Dirichlet Green function (field zero on outside sites), which links the
cube to sites it does not refresh. The carrier uses the opposite rule: no link out of the cube
(`ConfinedCarrier`, plain truncation). Applied to the colour field, no link out means no colour
flux leaves (`n·E = 0`, Neumann for the electric part) and, for the magnetic part, component
`k` has no link out along axis `k` (`n×B = 0`). These are the bag-model conditions, here from
the lattice rule. With them (`tools/colour_fluctuation.py`, now the default; `BC=D` for the
old one): N–Δ is `12 MeV` at `0.118`, so the observed `293 MeV` needs `α_s ≈ 2.9` (Dirichlet:
`5.6`; MIT bag fits: `≈ 2.2`), and at that coupling exchange moves `g_A` by only `−1.7%`, to
`1.353`. So one-gluon exchange does **not** close `g_A`; the Dirichlet result was an artefact
of the boundary. The cube's `g_A` is `1.35–1.38` against lattice QCD's `1.246(28)`.

**The Δ has no occupancy mass.** Masses in PMHadrons are occupancy costs of persistent
placements (`Occupancy`). The Δ decays strongly (`Γ ≈ 117 MeV`, lifetime `≈ 5.6×10⁻²⁴ s`),
about 3 time steps of the carrier cube (`ħ/(318 MeV) ≈ 2.1×10⁻²⁴ s`), far less than one
`Δ = 43`-step cycle. It is not persistent, so the minimum-room rule does not give it a mass;
its mass is a level of the carrier cube's dynamics, which needs the same colour coupling.

**Candidate: the hadron cube has 4 sites per edge (Nov 2026).** With a hard wall the carrier
is scale-free, so `g_A` depends only on the edge site count `n`: `1.377` (`3`), `1.265`
(`4`), `1.195` (`5`), `1.153` (`6`), toward the continuum bag value `1.09`. A rule that would
select `n`: `MinimalCube` asks for an interior vertex (a site all of whose links are the
volume's own), and `Occupancy` places one carrier per cell. If each persistent carrier needs
its own interior vertex, `k` carriers need `(n−2)³ ≥ k`: one carrier gives `n = 3` (the old
lepton cube), two or three carriers give `n = 4`. On `4³` (`1/a = 434 MeV` from the
carrier's rms radius `1.85` sites = `r_p`), with the no-link-out boundary, N–Δ needs
`α_s ≈ 2.4`, and exchange at that coupling gives **`g_A = 1.246`** (lattice QCD
`1.246(28)`, E8 `5/4`). Caution: the rule is proposed after seeing that `n = 4` fits, and the
coupling is still calibrated by the observed Δ.

**Verdict: not adopted — persistence as stated does not require it.** (1) `MinimalCube`'s
criterion is one interior vertex for the *volume*; nothing in it is per carrier. (2) The
carriers are not cell occupants in this computation: all three sit in the same spatial mode,
and exclusion is met by the antisymmetric colour (`ColourSinglet`, `CarrierStatistics`), so a
per-carrier site rule would contradict the model it is meant to fix. (3) "One cell per carrier"
in `Occupancy` is the meson ledger's lower bound, stated as an input there, and the nucleon's
base is the causal cone, not a cell count. (4) Economy picks the smallest valid volume, which
is `3³`. So `n = 3` stands and the `8%` stays open. The `4³` number is kept as a sensitivity
result: `g_A` is very sensitive to the carrier's resolution. Remaining candidates: virtual
colour-singlet pairs inside the cube (a pion cloud; the Toll bound covers only real emission
through the boundary), and the colour coupling without the Δ.

**Tried (Nov 2026).**
* *Pairs through colour exchange* (`PAIRS=1` in `tools/colour_fluctuation.py`: negative-energy
  intermediate modes, the Z-graphs): at the N–Δ coupling they move `g_A` by `+3.7%`, the wrong
  direction (net `+1.95%`, `1.404`). A pion cloud proper (a colour-singlet pair emitted by one
  carrier and absorbed by another) needs a carrier–pion vertex, which is not built.
* *Which operator is the axial current* (`tools/axial_ward.py`). A gauge boson couples to the
  walk through its links, so the spatial current is the velocity `v_z = i[H, z]`
  (point-split), and the axial one is `γ5 v_z`. On `3³` it gives `0.542` against the on-site
  `Σ_z = 0.826` (`g_A = 0.904` against `1.377`); the two converge only slowly as the cube grows
  (ratio `0.66, 0.74, 0.78, 0.80, 0.84` for `n = 3…8`). The target `0.75` lies between them.
  This is lattice QCD's `Z_A` problem: a bare lattice axial matrix element is normalized by an
  axial Ward identity before it is compared (typical `Z_A` for Wilson-type actions is below one;
  `5/4` needs `Z_A = 0.908` on the on-site operator).
* *Normalization — partly checked (Nov 2026, `tools/axial_ward.py`).* A free carrier moving
  along `z` gives `⟨Σ_z⟩ = 1` (its helicity) at every momentum, and the link current gives
  `cos k`. That checks the on-site operator's spin normalization for free axial motion; it is
  not a Ward identity for the confined current (review by a second model, Nov 2026: the script
  also mixes the slice-odd `Sγ5` with the slice-even `γ5`). The decisive check, not yet done,
  is the local axial variation of the actual two-slice update with the wall and inter-slice
  terms kept; it could confirm the on-site operator without an adjustable `Z_A`.

**Cross-checks that do not depend on the axial normalization (Nov 2026).**
* *Magnetic moment* (`tools/proton_moment.py`; the vector current is conserved, so no `Z`).
  SU(6) gives `μ_n/μ_p = −2/3` (measured `−0.685`). The size is low: on `3³` with the carrier
  rms radius set to `r_p`, `μ_p = 1.74` n.m. (on-site current) or `1.04` (link current),
  measured `2.793`; larger `n` raises it slowly (`2.11` / `1.67` at `6³`). MIT bag fits are also
  low (`≈ 1.9`). So the carrier core is too small or too relativistic for `μ_p` while too
  non-relativistic for `g_A`: one cube does not fit both. In hadron models the pion cloud
  raises `μ` and lowers `g_A`, which is the direction both need.
* *Goldberger–Treiman* `g_πNN = g_A m_N/F_π`: E8 `5/4`, `m_N`, `F_π = f_π/√2 = 92.1 MeV` give
  `12.74`; from `g_πN²/4π ≈ 13.7`, `g_πNN ≈ 13.1` (the usual `≈ 2%` GT discrepancy, plus the
  electromagnetic `2%`).
* *Big gaps elsewhere that point the same way:* the singlet axial charge (quark spin fraction)
  is `ΔΣ ≈ 0.3` measured against `0.83` here (the axial anomaly; `PMConstants.ChiralAnomalies`),
  and hyperon decays give `F/D ≈ 0.58` against SU(6)'s `2/3`.
So the strongest single lead is the pion cloud: it is the one mechanism that moves `g_A` down
and `μ_p` up together. It needs the carrier–pion vertex, and that vertex is fixed by the same
axial current (Goldberger–Treiman), so it and `Z_A` are one problem.

*Pion-cloud estimate (Nov 2026, floating point).* One loop with the Goldberger–Treiman vertex,
E8 `F_π = 92.1 MeV`, `m_π`, nucleon intermediate states only, and a dipole form factor:
`δg_A/g_A = −(1+2g_A²)/(12π²F²) ∫k⁴u²/ω³` (normalized to the chiral log). The sign is right,
but the size is set by the cutoff: `−19%`, `−39%`, `−65%` for `Λ = 600, 800, 1000 MeV`; the
cube's own form factor (dipole matching `r_p`) gives `Λ ≈ 810 MeV`. The nucleon-only loop is
known to overshoot: Δ intermediate states cancel much of it (exactly at large `N_c`), and there
is no E8 Δ. So the cloud can supply the `−9%`, but not without the Δ sector; this is not yet a
prediction.

**Second-model review (Nov 2026) — what is fixed and what is not.**
* *The ground-orbital Δ already exists.* Three carriers in the common ground doublet span the
  symmetric spin–flavour space `Sym³(4) = (S=I=½) ⊕ (S=I=3/2)`, dimensions `4 + 16 = 20`, both
  at energy `3E₀`. So the Δ multiplet is available without a Δ mass or occupancy rule.
* *The N–Δ cancellation is fixed for the cubic term.* With `G^{ia} = Σ_q σ^i_q τ^a_q/4` and a
  common static source, the double commutator `Σ[G^{jb},[G^{jb},G^{ia}]]` equals `G^{ia}` on the
  full 20 states, but `(5/3)²` times it with nucleon-only intermediate states. Checked
  numerically here: `1.000` and `2.778 = 25/9`. So the full multiplet keeps `9/25` of the
  nucleon-only cubic term. This is not a factor for the whole `−39%` (the term linear in the
  coupling and nonzero splittings differ).
* *The `−39%` is not a prediction.* Normalized to the chiral log, the integral still carries a
  `Λ²` piece whose split between core and cloud is free; a radius fixes a form factor's slope,
  not the emission matrix element across the zone.
* *The cube cannot split N and Δ as it stands.* Independent carriers give `3E₀` to both; a term
  `cJ²` respects every symmetry and moves the splitting by `3c`. The economical source is the
  same pion interaction: its static self-energy contains `−K Σ G^{ia}G^{ia}`, and
  `Σ G² = 3.5625` on N and `2.0625` on Δ (checked here), so it makes the **nucleon lighter** by
  `1.5K` with no colour coupling or observed splitting as input. `K` needs the pion modes and
  source.
* *Two persistence premises, different physics:* the host confines the pion **source** (pion
  propagates freely), or the host confines the pion **field** (discrete modes on the cube).
  The carrier's no-link-out rule does not by itself select the pion's boundary. Choosing it, the
  form factor, or `5/4` in the vertex because they give `−9.2%` would be a fit; the vertex should
  use the bare cube current.
* *Null test:* `μ_n + (2/3)μ_p` vanishes at every resolution in the one-body common-orbital model;
  measured `−0.051` n.m. A purely isovector cloud shifts it by `−δμ_p/3`, so raising `μ_p` from
  `1.04` to `2.79` that way would overshoot it tenfold: a cloud must also change the isoscalar
  part. Caveat on `tools/proton_moment.py`: it sets the bare carrier radius equal to the dressed
  charge radius, which a charged cloud invalidates.
**Plan:** (1) the local axial variation of the two-slice update (current and pion source from
one update); (2) the degenerate 20-state second-order self-energy with that source, giving the
vertex correction to `g_A` and `K` for the splitting, under each pion-boundary premise; (3) the
magnetic null test on any proposed dressing.

**First pass, no free parameters (Nov 2026, `tools/pion_cloud_cube.py`).** Pion source:
derivative coupling to the ground doublet's on-site axial density on the cube's interior links
(bare cube current, no `5/4`); `1/a = 318 MeV`, E8 `F_π = 92.1 MeV`, `m_π = 138 MeV`; static
second-order dressing on the 20 `N + Δ` states (degenerate result checked against the double
commutator).

| pion boundary premise | `δg_A/g_A` (N, Δ degenerate → physical splitting) | `Δ − N` from the cloud |
|---|---|---|
| field confined (no link out) | `−16.6%` → `−22.7%` | `172 MeV` |
| source confined (pion on the unbounded lattice) | `−5.8%` → `−7.6%` | `79 MeV` |
| needed | `−9.2%` (to `5/4`) | `293 MeV` observed |

Field-confined overshoots `g_A` (`1.06–1.15`); source-confined gives `1.272–1.297`, within the
lattice-QCD `1.246(28)`, and a cloud share of the splitting (`27%`) like the cloudy bag's
(about a third). Caution: the source-confined premise looks better *after* the numbers; the
a-priori case for it is that the pion is a colour singlet, not a resource of the host's colour
flux, so like the emitted electron (`PMElementaryParticles/CONTINUOUS.md`, rule 2) it is not
walled in; the case for field-confined is that its carriers are. Still to do: derive the source
from the local axial variation of the two-slice update (the wall gives a surface term), recoil
(non-static) corrections, and the magnetic null test.

*Last perturbative try.* Converting the one-loop `α_s(1/a) = 0.87` to the static-potential
scheme (`α_V = α(1 + a₁α/4π)`, `a₁ = 31/3 − 10n_f/9`) gives `α_V ≈ 1.3`, against the `2.9`
the N–Δ splitting needs with the persistence-consistent boundary. The coupling on the cube
stays a non-perturbative open item.
