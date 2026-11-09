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
(edge-identification); per-step maintenance is closed in PM-4 (`PerStepContract`). Open:
assembling the OS **quotient** (the null set `{F | osForm F F = 0}` is now the semi-inner-product's
kernel — `osCore_normSq_eq` — so the descended form on the quotient is the finite-dimensional
physical Hilbert space); the
microscopic E8 realization of the abstract hop, its physical readout and price law,
shared group/trace normalization across spacings, and the admission of the coherent
root-generator evolution as the substrate dynamics. For the packet subsystem this
reduces to the C² control one-forms and that admission. Gap half: `DefectGap` proves a
volume-uniform gap for PM's diagonal distinction cost (unique vacuum up to relabeling, every
excitation `≥ 1` transition, transfer contraction `≤ p` off the vacuum); `GapStability` proves the
gap survives a form-bounded perturbation with `ε < m/2`. Open, and the real content: a
volume-uniform bound on the off-diagonal (plaquette/kinetic) part of the gauge transfer matrix
restricted to what the readout sees, or a cluster-expansion replacement for it; identifying
`p` with the Gibbs `β`; and carrying the gap through the continuum readout. Remaining
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

## Downstream boundary

Generic proofs do not move a downstream paper's physical identification with them.
Paper III owns packet representations and constants; Paper IV flavour/mass; Paper V
decay/phase-space; Paper VI cosmology. See [`OVERVIEW.md`](OVERVIEW.md).

## Verification

Run `./build.sh PMAction` and `./build.sh audit`. No Paper III–VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
