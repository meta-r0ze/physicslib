# PMAction — open work

Checked mathematics, the module map and everything established are in
[`OVERVIEW.md`](OVERVIEW.md). This file lists only what remains. Each item needs a model law or a
new construction, not a missing Lean statement, unless marked otherwise.

## A. Open for the hadrons (active)

1. **The colour coupling inside a hadron.** The carrier cube's scale is `1/a ≈ 318 MeV` (candidate,
   below), at the confinement scale, so the ledger `α_s = 0.1180` (read at `M_Z`,
   `PMConstants.ReadoutScales`) cannot be run down. `CommonResponse` prices gauge loops and the
   fermion's Wilson term with one `toll·m`, but no value of `toll·m` (times Paper I's survival `β`)
   is fixed, and matching it to the fermion's normalization needs an action–cost identification
   for fermions that PM does not state. By `ReadoutScales`' principle (a readout is matched where
   it is maintained), the hadron's colour is read where it is maintained, per channel (Paper III's
   `12η` colour requirement). **Lower priority than it looked:** `FlatPersistence.flat_iff` and the
   singlet's vanishing mean colour density mean the persistent links carry no colour field, so the
   colour-magnetic correction to `g_A` enters only through fluctuations.
2. **The lattice-to-energy unit.** Settled for both cubes (`PMHadrons.CubeScales`): the carrier
   cube and the decay's lepton cube cannot share a spacing (E8 masses and radius force a factor
   `> 300`, `two_units`); each persistent system has its own minimal cube at its own scale. Carrier
   cube `a ≈ 0.621 fm` from the E8 proton radius (the carrier's rms radius, numerical); lepton cube
   `a_e = ħ/(√2 m_e c)` from the channel's own unit (`lepton_hop`), which fixes the Coulomb `κ`.
   Remaining here: the carrier rms radius `1.354` in Lean (it is a numerical eigenvector property).
3. **The photon loop's normalization in `ContactRunning`.** The coefficient's Dirac and charge
   structure is derived; the overall `(α/4π)` per unit, the `¼` direction average and the
   orientation sign are continuum inputs. Target: the substrate link response to a pair of
   charged legs, as `RunningResponse` did for vacuum polarization.

The `g_A` gap itself (`+8%` after every PMAction input is fixed) is now a PMHadrons question: the
next candidate is emission (`PMHadrons.EmissionSpace`, `TollGovernor.emissionWeight`). The PMAction
piece it may need is the carrier–pion vertex (the pion couples to the carrier's axial current).

## B. Foundational (long-term)

1. **Physical states and observations.** Justify the complex-amplitude/coordinate readout contract
   and the carrier class/wall allocation; identify any many-particle state space or its statistics
   algebra. Equal dimensions and reversible persistence do not select the physical state space.
2. **Primitive admission.** Derive admission and implementation of the local amplitude factors in
   the microscopic E8 gate library, and their prices; identify the directional-exponential
   completion with the on-site one.
3. **Prepared initial reference.** Closed basis-preserving controls cannot supply it
   (`ReferenceSourceBoundary`, `PrimitiveRecordBoundary.cannot_prepare`); its per-tick ledger and
   the physical allocation of the reference/record banks remain.
4. **Clock and event ledger.** Price the setup, controls, transport/source/export and maintenance.
   Four factor applications are not four primitive E8 events; survival minimization orders a
   supplied cost but does not determine it.
5. **Microscopic gauge transport.** The E8 realization of the abstract hop, its readout and price
   law, shared group/trace normalization across spacings, and admission of the coherent
   root-generator evolution as the substrate dynamics (for the packet subsystem: the `C²` control
   one-forms and that admission). Reopens the gauge gap only if PM derives `β` or identifies the
   Wilson cost with the survival cost (connects to A.1).
6. **Full field and integrated limits.** Real-space field/PDE mode–domain control, the integrated
   Hessian, the full real-space fermion field, interacting-field estimates.
7. **Applications.** Normalization, measure and regulator (and the trace/running reading); gravity
   and measurement need their own state/update/observable; quantum continuum and Lorentzian
   continuation are distinct obligations.

## Out of scope

The quantum Yang–Mills constructions (transfer matrix, infinite volume, full O(4) restoration,
renormalized continuum, continuum mass gap); see the scope note in [`OVERVIEW.md`](OVERVIEW.md).

## Downstream boundary

Generic proofs do not move a downstream paper's physical identification with them. Paper III owns
packet representations and constants; Paper IV flavour/mass; Paper V decay/phase-space; Paper VI
cosmology.

## Verification

Run `./build.sh PMAction` and `./build.sh audit`. No Paper III–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
