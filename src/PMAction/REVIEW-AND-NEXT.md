# PMAction — open work

Checked mathematics, the module map and everything established are in
[`OVERVIEW.md`](OVERVIEW.md). This file lists only what remains. Each item needs a model law or a
new construction, not a missing Lean statement, unless marked otherwise.

## A. Open for the hadrons (active)

1. **The colour coupling inside a hadron: closed at leading order.** `ColourSinglet` shows the
   three-carrier singlet in one spatial mode has zero mean colour charge and current
   (`singlet_mean_one/two/three`: every traceless one-body colour operator averages to zero), and
   `FlatPersistence.flat_iff` shows unsourced persistent links are flat. So no colour-magnetic
   field acts on spin at leading order. The fluctuation correction would use the gauge `β`,
   which is fixed downstream (B.5); the cube-scale `α_s` is not needed.
2. **The lattice-to-energy unit.** Settled for both cubes (`PMHadrons.CubeScales`): the carrier
   cube and the decay's lepton cube cannot share a spacing (E8 masses and radius force a factor
   `> 300`, `two_units`); each persistent system has its own minimal cube at its own scale. Carrier
   cube `a ≈ 0.621 fm` from the E8 proton radius (the carrier's rms radius, numerical); lepton cube
   `a_e = ħ/(√2 m_e c)` from the channel's own unit (`lepton_hop`), which fixes the Coulomb `κ`.
   Remaining here: the carrier rms radius `1.354` in Lean (it is a numerical eigenvector property).
3. **The contact running, remaining step.** Derived: Dirac and charge structure
   (`ContactRunning`, `ContactFierz`), the `¼` from the D₄ roots, the unit `(α/4π)ln(M²/μ²)` from
   the 4D measure (`LoopMeasure.log_unit`), the self-energy weight `W = −1`
   (`self_energy_weight`) and the orientation sign (`weights_from_orientation`). Still the
   continuum's: the Feynman parametrization step and the identification of the leading-log region
   with the lattice sum far below the cutoff. A lattice version (the D₄ sum approaching the
   integral) would close it; low priority, since `R` already matches the pion to `7×10⁻⁵`.

The `g_A` gap itself (`+8%` after every PMAction input is fixed) is now a PMHadrons question: the
next candidate is emission (`PMHadrons.EmissionSpace`, `TollGovernor.emissionWeight`). The PMAction
piece it may need is the carrier–pion vertex (the pion couples to the carrier's axial current).

## B. Foundational (long-term)

1. **Physical states and observations.** Three pieces, each to be derived from PM:
   (a) the readout rule: **done**, `ReadoutRule.born` (an additive, basis-invariant, monotone
   readout weight is `r²`); (b) the carrier class allocation: **done**,
   `ClassAdmission.all_classes_admitted` (the observed vacuum is class-symmetric, so the admitted
   set of most-persistent classes is permutation-invariant and nonempty: all three);
   (c) many-particle statistics: **done**, `CarrierStatistics` (exchange acts as `±1`; with the
   geometric premise that an exchange in three spatial dimensions is a relative full turn, the
   phase is the spin-½ full turn `−1`, matching `CarrierParity`; antisymmetry and exclusion
   follow). At most 24 carriers per site's observed modes; this is not the `nodeCapacity` 32.
2. **Primitive admission.** Derive admission and implementation of the local amplitude factors in
   the microscopic E8 gate library, and their prices; identify the directional-exponential
   completion with the on-site one.
   **Prices are fixed downstream (found Nov 2026).** Survival sees only the product `toll·m`
   (with Paper I's `β`), never `toll` and `m` separately, so they need no separate derivation.
   `PMConstants.EventStiffness.calibration` and `ChainCouplings.chain_calibration` fix the product
   from the electric coupling: `e² = 1/(toll·m·N_sys) = 4πα` (Paper I's `α`, Paper III's footprint
   `N_sys`), which gives every primitive event a price. (`PMSubstrate.tollTerm`, a probability, is a
   different object.) What remains here is admission: which local amplitude factors the E8 gate
   library implements.
3. **Prepared initial reference: closed by selection** (`ReferenceSelection`, Nov 2026). PM does
   not require dynamics to prepare the reference: the survival law selects it, and the most
   persistent configuration is the uniform background (`selected_reference`). Its per-tick ledger
   is one clean record consumed and one exported per tick at the coupling site
   (`one_record_per_tick`), from distinct sites on an open orbit (`consumed_records_distinct`);
   maintenance is exact forever (`reference_forever`) and needs the unbounded substrate
   (`needs_unbounded`). Remaining, small: a formal map from the background `Config` to
   `RecordSupply`'s stream (now an identification in the docstring), and the physical allocation
   of the reference/record banks (with B.1).
4. **Clock and event ledger.** With `toll·m` fixed (B.2), the prices are numeric once the events
   are counted. Remaining: the event count of the setup, controls, transport/source/export and
   maintenance. Four factor applications are not four primitive E8 events; which primitive events
   a factor application costs is the open count.
5. **Microscopic gauge transport.** The gauge `β` is derived downstream:
   `CarrierResponse.common_response_limit` gives `β = toll·m·W/2`, and with the calibration above
   `g² = 1/(κ_R·toll·m·W)` for each sector's ledger `W` (`PMConstants.ChainCouplings.
   chain_couplings`: weak, hypercharge, colour). Remaining here: the E8 realization of the
   abstract hop, shared group/trace normalization across spacings, and admission of the coherent
   root-generator evolution as the substrate dynamics (for the packet subsystem: the `C²` control
   one-forms and that admission).
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
