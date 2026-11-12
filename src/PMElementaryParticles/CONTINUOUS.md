# From a lattice to the continuum

The substrate is a lattice. It has discrete sites, discrete links and a discrete clock.
But many results in this library use continuous mathematics: integrals, `π`, spheres and
phase space. This note tells you why that is correct, and when it is not correct.

## The short answer

The lattice does not change. Continuous values come from it in two ways: as a limit when the
physics is large compared with the spacing, and as a bound that every discrete shape approaches.

* When a process is much larger than the spacing, a sum over sites is very close to an
  integral. Then we use the integral.
* When a process is only a few sites wide, the sum is not close to an integral. Then we use
  the sum.

Persistence tells you which case applies. It does not leave the choice to the modeller.

## Rule 1: a persistent volume has walls

A hadron is a persistent volume. Only its own sites are refreshed. Sites outside it are not
its resources. Thus the volume has a hard wall, and its modes are discrete.

* The smallest such volume is the `3×3×3` cube (`PMAction.MinimalCube`).
* The light carrier lives on that cube (`PMAction.ConfinedCarrier`, `ConfinedWalk`).
* Here you must use the lattice. Its sums and its edge sites are the physics.

## Rule 2: a particle that leaves has no walls

An emitted particle leaves through the Toll boundary (`PMHadrons.TollGovernor`). No persistent
volume refreshes it, so nothing confines it. Its modes are the modes of the unbounded lattice
at its own spacing.

When the energy is small compared with the inverse spacing, those modes are very close to
continuum modes. Sums over them become integrals. This is the usual continuum limit of a
lattice. It is a limit of the lattice, not a second model on top of it.

## Rule 3: symmetry carries over

The link directions are the 24 `D₄` roots. Their moments are the same as those of a
rotation-invariant distribution through fourth order (`PMAction.D4Isotropy`). Thus low-order
lattice sums have the same angular form as continuum integrals. For example, the `¼` in the
contact running is a `D₄` direction average (`PMAction.ContactRunning.loop_direction_average`).

Caution: this is a statement about root moments. The library does not prove full rotation
invariance of every lattice correction (see the Yang–Mills scope note in `PMAction/OVERVIEW.md`).

## Example: the neutron's electron

Neutron decay shows all three rules (`PMHadrons/REVIEW-AND-NEXT.md` §2,
`tools/beta_channel_modes.py`).

1. An older template put the emitted electron on its own `3×3×3` cube. That gave
   `948.7 s`. But the electron is not part of a persistent volume, so Rule 1 does not apply.
2. Make the electron's cube larger, at the same spacing. The open-mode fraction goes from
   `0.453` (`3³`) to `0.741` (very large cube). Thus the small cube was a choice, not a result.
   The small-cube template also fails for other decays: it gives a tritium rate that is about
   3000 times too large.
3. Apply Rule 2. The electron's modes are continuum modes. The rate then uses the same phase
   space as the muon (`PMElementaryParticles.MuonRate`, `PolarMeasure`). All inputs are E8
   values. The result is `954.3 s` without the proton's Coulomb pull and `923.4 s` with it
   (`PMHadrons.NeutronContinuum`). The electron's own low-energy QED, on the same route, gives
   `909.2 s`. The measured value is `878.4 s`. The rest is the axial coupling `g_A`.
4. The small cube was `0.6%` from the continuum value without Coulomb. That was a coincidence of
   the neutron's energy, not a law.

The Coulomb pull shows the same thing. On the small cube the electron has one fast mode, and
the pull is `1.1%`. Over the continuum spectrum the pull is `3.4%`. The difference comes from
slow electrons. The small cube has none (`tools/lepton_coulomb.py`).

## Example: `π` in `α⁻¹` (Capacity)

`α⁻¹` contains the Capacity term `πΔ` (`PMSubstrate.CapacityBarbier`). Here the continuum
appears in a different way. It is not a limit of small spacing. It is the largest value that
any shape made of nodes can reach.

1. A cycle is a closed boundary. Causality limits it: any two points on it are at most `Δ`
   apart, because a signal must cross and return in one cycle (`CapacityEnvelope.width_le`).
2. Make the boundary from nodes. It is then a polygon: straight edges between nodes. Its length
   is the sum of the edges (`CauchyPolygon`). Every such polygon has length at most `πΔ`
   (`perimeter_le_of_causal`).
3. Add more nodes. A regular polygon with `n` nodes on a circle of radius `r` has length
   `2nr·sin(π/n)`. This is less than `2πr` and more than `2πr − rπ³/(3n²)`
   (`CircleLength.inscribed_sum`). The gap goes to zero as `n` grows.
4. The circle is the least upper bound of all these polygons. Its length is exactly `πΔ`
   (`CircleLength.circle_length`, `CauchyPolygon.capacity_is_max_length`).

So the nodes are discrete, and each path between two nodes is a straight segment. The
continuous value, `π`, is not added to the lattice. It is the limit that every node boundary
approaches and none goes past. The shape is a circle in a plane, not a sphere. Its value does
not depend on the shape: every boundary of constant width `Δ` has length `πΔ`
(`CapacityBarbier.barbier`).



| Result | Continuum object | Where |
| --- | --- | --- |
| Muon width, `192π³` | three-body phase space | `PMElementaryParticles.MuonRate` |
| `Φ₂ = 1/(8π)` | `ℝ³` momentum integral and energy shell | `PMElementaryParticles.PolarMeasure` |
| One-loop running unit `(α/4π) ln(M²/μ²)` | 4D shell integral, far below the cutoff | `PMAction.LoopMeasure` |
| Neutron lifetime | phase space and Fermi factor | `PMHadrons.NeutronContinuum` |

## Places that must stay on the lattice

| Result | Why | Where |
| --- | --- | --- |
| The light carrier and its spin fraction | it is confined to a persistent cube | `PMAction.ConfinedCarrier` |
| The proton's charge potential on the cube | exact Green function of the cube | `PMAction.CubeGreen3` |
| Hadron colour coupling | the cube scale is near the strong-coupling region | `PMAction/REVIEW-AND-NEXT.md` A.3 |

## What is proved

The continuum objects are proved in Lean: the integrals, the measures and the bounds.
That a lattice sum approaches its integral far below the cutoff is the standard limit. The
library checks it with numbers (the tools above). It does not prove it in general. A general
proof for interacting fields is out of scope (`OPEN-PROBLEMS.md` §4).
