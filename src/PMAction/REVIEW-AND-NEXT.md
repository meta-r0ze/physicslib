# PMAction — open work (todo)

Checked mathematics and the module map are in [`OVERVIEW.md`](OVERVIEW.md). This
file is only what remains. Paper II builds clean; run `./build.sh PMAction` for current counts.

Once-listed inputs (carrier statistics, the even-mode completion, the projector/
mediator, the V−A trace, exact record maintenance, the transport ODE, the clock
period) are now **derived** and documented in `OVERVIEW.md`. The remaining items
each need a **model law or a new construction**, not a missing Lean statement:

## 1. Physical states and observations
Proved: native representation, dependent-sector observation (`SectorObservation`),
class bundle (`CarrierClassBundle`), and the odd-carrier sector + identity even modes
(above). Open: justify the complex-amplitude/coordinate readout contract and carrier
class/wall allocation; identify any many-particle state space or its statistics algebra.
Equal dimensions and reversible persistence do not select the physical state space.

## 2. Primitive admission and physical completion selection
Proved: `LocalIsometricDynamics` gives the finite-support on-site completion (unitary on
all labels, same stencil, all-state readout); `CompletionSelection` shows **persistence
selects it** among completions (`most_persistent_completion`, `selected_is_identity`).
Open: derive admission/implementation of the local amplitude factors in the microscopic
E8 gate library and their prices; the directional-exponential completion is still not
identified with the on-site one.

## 3. Reference, records and vacuum coexistence
Proved: `RegisterReference` (capacity-aware spatial model), exact maintenance
(`RecordSupply`, `HomogeneousRouting`), stationary-preparation bounds
(`PersistentBackground`, `ReversibleStationarity`), and **unboundedness from
persistence** (`HomogeneousRouting.forever_iff_open`, `forever_needs_infinite`:
persistence forever forces an infinite substrate). Open: the **prepared initial
reference** — closed basis-preserving controls cannot supply it
(`ReferenceSourceBoundary`, `PrimitiveRecordBoundary.cannot_prepare`) — its per-tick
ledger, and physical allocation of the reference/record banks.

## 4. Physical clock and event ledger
Proved: `RegisterSplit` (four-phase schedule, exact phase/tick readout),
`ClockDynamics` (unitary on coherent clock amplitudes), `ClockPeriod` (the period is the
substrate `Δ`). Open: price setup, controls, transport/source/export and maintenance.
Four factor applications are not four primitive E8 events; survival minimization orders
a supplied cost but does not determine it.

## 5. Microscopic gauge transport and smooth refinement
Proved: `CompositionalTransport` (transport ODE + classical limit from conserving
single-hop updates under subdivision + C² response); `NativePacketUpdate` (contracts for
the native E8 packet subsystem); `GeometricGauge`, `ReciprocalReflection`
(gauge/Gibbs/site-reflection positivity); `OsterwalderSchrader` (OS form
`ReciprocalReflection.osForm` + `reflection_positive'`; `conj_symm_of_real_diag`, `osCore`,
`os_cauchy_schwarz` — the OS form is a Hermitian **semi-inner-product** with Cauchy–Schwarz, the
`PreInnerProductSpace.Core` algebraic OS step); `QuotientClosure.gibbs_quotient_invariant`
(edge-identification); per-step maintenance is closed in PM-4 (`PerStepContract`). The OS **quotient is assembled**: the null set is the semi-inner-product's kernel
(`osCore_normSq_eq`, `mem_osNullSubmodule_iff`), null vectors pair to zero (`osNull_cross`,
`osNull_cross_right`), the form descends (`quotientForm`), and `quotientCore` +
`quotientInnerProductSpace` make `V ⧸ osNullSubmodule` an `InnerProductSpace` — the physical
Hilbert space. Open: the
microscopic E8 realization of the abstract hop, its physical readout and price law,
shared group/trace normalization across spacings, and the admission of the coherent
root-generator evolution as the substrate dynamics. For the packet subsystem this
reduces to the C² control one-forms and that admission. Gap half: `DefectGap` proves a
volume-uniform gap for PM's diagonal distinction cost (unique vacuum up to relabeling, every
excitation `≥ 1` transition, transfer contraction `≤ p` off the vacuum); `GapStability` proves the
gap survives a form-bounded perturbation with `ε < m/2`. The substrate gap is
closed: `MassGap.SlabGap.slab_gap_explicit` (flip-even sector of `T²`: simple top `Λ`, rest
`≤ qΛ`, uniform in volume; mass `≥ β/2` per tick, `CubicBox.box_mass_gap`; see
`MassGap/README.md`). The gauge layer is a separate continuous field
(`NativePacketRouting.pure_permutation_refinement_trivial`), so its gap is not an open item here:
it is the quantum Yang–Mills problem below. It reopens only if PM derives `β` or identifies the
Wilson cost with the survival cost. Remaining
quantum-Yang–Mills constructions (transfer matrix, OS quotient/Hilbert space, infinite volume,
full O(4) restoration, renormalized continuum, mass gap of the continuum theory) are out of
scope; see the Yang–Mills scope note in
[`OVERVIEW.md`](OVERVIEW.md).

## 6. Full field and integrated limits
Proved: `JointSpaceTime` (fixed-momentum joint limit), `UniformGaugeAction`/
`IntegratedGaugeAction`/`IntegratedScalarAction`/`ClassicalYangMills`/`LatticeSiteAction`
(site-sum-to-integral limits on a box under explicit regularity, with the transport ODE
constructed), `LatticeToContinuum` (pointwise Hessian-density limit). Open: full
real-space field/PDE mode–domain control, the integrated Hessian, the full real-space
fermion field, and interacting-field estimates.

## 7. Physical applications
Proved: the chiral projector is forced on the zero kernel (`projector_unique_on_kernel`)
and equals block-diagonal `P_L` globally (`projector_eq_fromBlocks_PL`); the weak
representation is attached (`WeakCurrentBridge`,
`ReferenceStabilizer.electroweak_stabilizer`); statistics (carrier parity) and the
mediator (broken electroweak direction) are E8. Open: normalization, measure and
regulator (and the trace/running reading), each a construction; gravity and measurement
need their own state/update/observable; quantum continuum and Lorentzian continuation
are distinct obligations.

## 8. What the hadron decays need from here (found in PMHadrons, Nov 2026)

Working the neutron, pion and kaon widths in the six-pillar template (`PMHadrons.DecayInstantiation`)
left three gaps; each is a missing construction here, not in PMHadrons:

1. **A confined light carrier.** Built: `ConfinedCarrier` (two-slice Hamiltonian on a finite
   region is Hermitian; the wall preserves `Σ_z`), numerics in `tools/confined_carrier.py`. The
   wall is hard by persistence: sites outside the hadron's cube are not its resources, so they
   are not refreshed and carry no amplitude (`M_out = ∞`). On the `3×3×3` cube this gives
   `⟨Σ_z⟩ = 0.826`, a single free carrier's `(5/3)⟨Σ_z⟩ = 1.377` (`+8%`; not the neutron's
   `g_A`; the Wilson carrier gave `+17%`). The number depends only
   on the edge site count, which `MinimalCube` fixes at 3. Open: the remaining `+8%` is beyond the
   single free carrier, in the three carriers' mutual synchronization (gluon dressing), and the
   discrete-time version is still to be built.
   **Walk version** (`tools/confined_walk.py`): `CompletionSelection` applied to each axis step
   leaves the face modes the truncated hop misses unchanged (`R_j = cos τ N_t² + i sin τ N_t +
   P_j`), which is unitary, local, and has the plain truncation as generator. So the hard wall is
   the walk's wall, and the truncation's `⟨Σ_z⟩` levels off toward the bag value as the cube grows
   (`0.826 → 0.677` for edge `3 → 7`). The tick: in Paper II's
   vacuum-preserving update the axis steps are ordered, so finite `τ` makes the carrier anisotropic
   (speeds `sin τ (cos 5τ, cos 3τ, cos τ)`, `VacuumTangent`; on `3³` at `τ = 0.3`,
   `⟨Σ_x, Σ_y, Σ_z⟩ = 0.785, 0.797, 0.776`). The cube's isotropy then fixes the small-tick regime
   (`VacuumErrorRate`), where the carrier is the Hamiltonian's `0.826`. (An earlier scan with the
   uncorrected ordering, which Paper II warns against, showed spurious reductions.) Also checked: the physical axial density with
   `γ⁵ = Γ = −iα₁α₂α₃` (`WallChiralCurrent`, `VATrace`) is `Σ_z`, and projecting onto the
   zero-mode chiralities raises the value (`0.867` on `3³`), so the operator is not what is missing.
   Lean: `ConfinedCarrier.axisStep_unitary` (the identity-completed axis step is unitary for any
   Hermitian hop with `N³ = N`), `coefficient_partial` (`c c† c = c`), and `ConfinedWalk`
   (`truncHop_cube`: `N³ = N` for any partial-isometry shift; `shift3_partial` and the three cube
   axes; `cube_axisStep_unitary`: the walk on the `3×3×3` cube is unitary for every `τ`).
   **Status, recorded so it is not fitted:** every input is fixed (count, cube, hard wall, Wilson
   point, small tick, `Σ_z`), and the single free carrier gives `1.377` (+8%). The gap is what a
   free carrier leaves out. Next candidates: carrier–carrier interaction that touches spin or
   position, and the pion emission space. Rejected as fits: 4-site cube, soft wall, finite tick,
   `25/27`.
   **Carrier–carrier channels in PMAction (Nov 2026 survey):** pure colour routing leaves spin and
   position unchanged (no effect). Load on the links (`SpatialResponse`, clock speed `(ν−K)/ν`):
   the other two carriers' density gives `K/ν ≈ 0.004`; even an exaggerated 20% central slowdown
   moves `⟨Σ_z⟩` by 0.5%, so it is ruled out. Colour Coulomb (`CoulombKernel`): for a singlet with
   all three carriers in one mode the mean field vanishes and the exchange term does not reshape
   the mode. Colour-magnetic coupling through the gauge links (`GaugeTransport`, `CommonResponse`)
   is the remaining candidate. It touches spin and mixes the ground `G6` level with excited `G6`
   levels (the first, at `E = 1.543` on `3³`, has `⟨Σ_z⟩ = 0.10`), so it lowers `g_A`. Its size
   needs the colour coupling at the cube scale, which is not fixed (`D4Gauge`: `β` free; the E8
   `α_s` is at `M_Z`). Blocked on the same scale link as 8.2.
2. **The lattice-to-energy unit.** Candidate (Nov 2026, `tools/confined_walk.py`): the proton's
   charge radius is the rms radius of its carriers' charge, which for three carriers in one mode
   (`2/3 + 2/3 − 1/3 = 1`) is the mode's rms radius, `1.354` sites on `3³`. With the E8
   `r_p = Dħ/(m_p c) = 0.8412 fm` (`PMHadrons.protonRadius_value`) one site is `a = 0.621 fm`,
   `1/a = 318 MeV`. Independent check, not fitted: the carrier's lowest level `0.841/a = 267 MeV`,
   three carriers `≈ 800 MeV` against the nucleon's 939 (−15%, free carriers, no binding). Inputs:
   the free single-carrier mode and the charge-radius identification.
   **It does not fix the Coulomb `κ`.** The neutron's spectral channel reads the same `3³` cube's
   eigenvalues in units of `m_e` (`PMElementaryParticles.BetaLattice`), which puts that cube's
   site at `a_e = 1/(√2 m_e) ≈ 273 fm` (non-relativistic) or `1/m_e ≈ 386 fm` (Dirac), about
   450–600 times the carrier cube's `0.621 fm`. So "the `3³` cube" carries two different physical
   spacings: the hadron's carriers and the decay's final-state lepton modes. Either they are two
   different cubes (same `MinimalCube` geometry, different readout scale), or one of the two
   readings is wrong. The lattice Coulomb acts on the electron, so its `κ` belongs to the lepton
   cube and stays open. One statement of the spacing does not fix both, contrary to the
   original framing of this item ("one statement of the spacing fixes both").
   **Colour coupling at this scale (open).** `1/a ≈ 318 MeV` is at the confinement scale, so the
   ledger `α_s = 0.1180` (read at `M_Z`, `PMConstants.ReadoutScales`) cannot be run down
   perturbatively. The PM-native route is the gauge `β` on the cube lattice. `CommonResponse`
   prices a minimal loop at `toll·m·(1 − Re tr U/N)/2` per carrier-averaged flag, the same
   `toll·m` that prices the fermion's Wilson flag; but no value of `toll·m` (times Paper I's
   survival `β`) is fixed anywhere, and matching it to the walk's fermion normalization needs an
   action–cost identification for fermions that PM does not state. By `ReadoutScales`' own
   principle (a readout is matched where it is maintained), the coupling inside a hadron is read
   where the hadron maintains its colour, per channel (Paper III's `12η` colour requirement).
   Deriving that readout is the open step.
   **What persists inside the hadron (Nov 2026; the flat-link part is `FlatPersistence.flat_iff`):**
   - Not each carrier's colour: routing keeps re-addressing it. What persists is the singlet
     relation among the three channels, which every routing leaves invariant and which is
     invisible outside (zero external cost, Paper V).
   - Each carrier's spin and position persist under routing (`ColourRouting`: the boundary map is
     unchanged), so routing alone cannot move `⟨Σ_z⟩`.
   - The links: every curved minimal loop raises flags at the common toll (`CommonResponse`), so
     the most persistent link configuration is flat, by the same positive-change-price argument
     as `PersistentBackground` and `CompletionSelection`. The singlet's mean colour density and
     current vanish at every site for three carriers in one mode, so nothing sources a mean field.
   Consequence: at the persistence optimum there is no colour-magnetic field acting on spin; what
   remains is the fluctuation part, suppressed by the toll. So the colour coupling at the cube
   scale is not needed for the leading `g_A` correction, and colour-magnetic coupling is unlikely
   to be the `8%`. Next candidate: emission (the hadron spending part of its time with a pion
   emitted, `PMHadrons.TollGovernor.emissionWeight`, `EmissionSpace`). That moves spin into the
   pion's orbital motion, and it is priced by persistence.
3. **Spin and orbital response from the substrate.** Done in `RunningResponse`: the spin term
   `(2s)²` from the Clifford relations (`zeeman`, `concrete_spin`; spin 1 by
   `GaugeFluctuation.vector_kernel`), the orbital `−1/3` from the Landau sum (`landau_sum`,
   `pair_kernel`, `pair_coefficient`), assembled in `spin_term_from_response`. The weak contact's
   own coefficient is now `ContactRunning` (Nov 2026): within a bilinear the Ward combination gives
   `½W(Q₁−Q₂)²`; across bilinears the Dirac factors are `16` (same orientation) and `4`
   (opposite), with Paper II's matrices; assembled, `c = 3Q = (3/2)(1 + 2Q̄)` for any quark pair
   `(Q, Q−1)` and lepton pair `(−1, 0)`, `c = 2` for `u, d`; `PMHadrons.ShortDistanceRunning.
   runningFactor_from_contact` uses it. Still open: Lean proofs of the two tensor identities
   (checked numerically, `tools/contact_running.py`), and the photon loop's overall log
   normalization (`(α/4π)` per unit, the `¼` direction average, the orientation sign) from the
   substrate's link response, as `RunningResponse` did for vacuum polarization.

## Downstream boundary

Generic proofs do not move a downstream paper's physical identification with them.
Paper III owns packet representations and constants; Paper IV flavour/mass; Paper V
decay/phase-space; Paper VI cosmology. See [`OVERVIEW.md`](OVERVIEW.md).

## Verification

Run `./build.sh PMAction` and `./build.sh audit`. No Paper III–VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
