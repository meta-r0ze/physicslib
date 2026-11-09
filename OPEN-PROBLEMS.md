# OPEN-PROBLEMS — the register of what is not yet derived

The Lean tree is the ground truth for what is *checked*. **This file lists only the open
items** — the residues where a claim is conditional rather than derived. Closed results
are not listed here; see [`SCOPE.md`](SCOPE.md) and each module's `REVIEW-AND-NEXT.md`
for what is proved.

For each item: *why a reader flags it*, *what the E8 substrate / persistence would have
to produce* to close it, and *the quickest test*.

## Kinds

| kind | meaning | how it closes |
| --- | --- | --- |
| **H** | hypothesis — derivable, method known, not done | run the derivation |
| **P** | postulate — a physical premise | state once, stop calling it derived |
| **C** | construction — an object/machine to build | build it |
| **M** | model input — external data or a selected law | state once / measure |
| **X** | out of scope — general problem beyond PM | scope note |

**The persistence test** (`PersistenceMechanics.SelectionSymmetry`). Before calling
any discrete choice an input, ask: *is it the unique minimizer of a cost over an
explicit option family?* If yes it is **H** — derive it. If the symmetry is
continuous the choice provably ties and it stays **M** (`SelectionSymmetry.invariant_cost_tie`,
`exists_tied_of_moved`).

---

## P1 — open postulates, inputs and constructions

| ID | Item | Modules | Kind | What must be produced | Quick test |
| --- | --- | --- | --- | --- | --- |
| S1 | **Postulate L — the address lattice.** Additive discrete address structure + integral quadratic cost. | `PMSubstrate/Address.lean` | **P** | `Address.integer_coordinates` / `integer_gram_representation` / `finite_budget_gram` derive `Λ ≅ ℤⁿ` and an integral positive-definite Gram from the address/cost premises. The **finite generation is a genuine additional premise**: `ℤ^{(∞)}` (`Address.finsupp_not_finite_generated`) and the infinite-rank even lattice `D_∞ = {x ∈ ℤ^(∞) : Σxᵢ even}` (`Address.DInf`, `Address.two_smul_mem_DInf`) have finite cost levels and satisfy bit-addressing (`2Λ* ⊆ Λ`), yet are not finitely generated (`Address.DInf_not_finite`). | Postulate L once; the f.g. cannot be derived from Finiteness + bit-addressing. |
| S4 | **E8 → clock / sectors / costs.** Why the vacuum *uses* the E8 clock, sectors, events, weights, saturation. | `PMSubstrate` (`Clock`, `Sectors`, `NetCost`) | **P** | Δ = 43, ν = 16, σ = 5, χ = 2 are forced **given** the postulates (`persistence_selects`); the postulates themselves are the input (`VacuumIndependence` gives per-postulate counterexamples — the set is minimal/independent). | State the postulates once; no further derivation is available. |
| R1 | **Readout admission.** Admitting the complex-amplitude/coordinate readout as physical. | `PMAction.Machine.CarrierClassBundle`, `CarrierParity` | **M** | The readout **is built** (`CarrierClassBundle.isometry`, `generator_observed` + `evolution_readout`, `CarrierParity.range_iff_odd`/`projector`, `carrier_exchange_parity`; `readout_contract` packages it). The *admission* of this readout (and of the three classes simultaneously) is the modelling boundary. | Admit once; the contract is a theorem, the admission is not. |
| E6 | **Measure normalization.** Continuum density, electron measure, parent flux, overall normalization. | `PersistenceMechanics.ChannelMeasure`, `PMElementaryParticles` (`PolarMeasure`, `MuonRate`) | **M** | The counting measure is persistence-selected (`probability_uniform_of_const_weight`, `probability_perm_uniform`). The **continuum density `1/(32π²)` is grounded** (`PolarMeasure.continuum_angular_density`: `= (1/4π)·Φ₂`, both factors derived — `sphere_area_three`, `two_body_phase_space`), and the **electron measure is derived** (`electron_measure_from_integral`, `massless_lorentz_measure`). The spectral modes/weights are the E8 `BetaLattice` template. Remaining: the relativistic `2E` flux convention (`MuonRate.parentFlux`) and the readout normalization. | Count/density/electron-measure derived; only the `2E` convention + readout remain. |
| K1 | **Gauge-work price scale.** | `PMConstants.ControllerIdentification` | **M** | The minimal-cost repair is selected (`gaugeController`, cost `21`, `gaugeController_mixing`); the *overall price scale* is the input. | Selection done; price scale stated once. |
| R3 | **Prepared initial reference.** | `PMAction.Machine.PrimitiveRecordBoundary` | **M** | The obstruction is a theorem (`cannot_prepare`: no basis-preserving gate supplies the required two-support state); the *supplier* (a preparation/source contract) is the input. | Obstruction proved; supplier stated once. |

## P2 — open derivable leaves

| ID | Item | Modules | Kind | What is open | Quick test |
| --- | --- | --- | --- | --- | --- |
| A1d | **Heavy deformation shape (N > 146).** | `PMAtoms` §1 | H/M | Holdout even-even actinides scatter ±0.019 u; needs a Z-dependent/mid-shell factor. | Candidate ranking done; shape not yet predictive. |
| A2c | **Nuclear charge tail.** | `PMAtoms` §2 | M/H | The 3×3×3 charge response is exact; heavy scaling needs a finite-size differential. | Low-Z-anchored differential. |
| A3c | **Deformed proton closure `2(Δ+σ)=96`.** | `PMAtoms` §3 | **H** | Candidate; simple closure overcorrects U-238. | Refine the closure. |

## P3 — model-input leaves (data / selected laws; state once)

| ID | Item | Modules | Kind | Note |
| --- | --- | --- | --- | --- |
| F1 | Wall anchor magnitude δ | `PMFlavor` | M | Direction/functional form E8; magnitude has no cost functional (`unitWall`, `ckmWall` anchors). |
| F2 | Absolute wall-mass scale | `PMFlavor` | M | Ratios E8 (`capacity_ratio_sq`, `coupling_ratio`); scale external. |
| C1 | Dark ratio `31/6` vs `25/6` | `PMCosmology` (`Scaling`) | M | Both proved distinct; which is `Ω_DM/Ω_b` is recorded as input. |
| A7 | Electron screening/exchange, Aufbau order | `PMAtoms` §6 | M | Fill order is a supplied input (hydrogenic `−R∞/n²` has no ℓ-dependence). |
| C1–C7 | Cosmology Part B | `PMCosmology` | M/C | State/clock/readout, background `L(a)`, primordial source, baryon-changing event, metric/causal structure, entropy normalization, joint test. |
| E7 | Decay law / physical E8 tick | `PMAtoms.E8Tick`, `E8TickUnit` | M | The E8 tick is the clock period `Δ = 43` (`E8Tick.e8Tick_eq`); the **SI conversion** (`E8TickUnit`) is a comparison input, explicitly not E8-derived. |
| — | Nuclear rate unit `β·c0` (absolute attempt frequency) | `PMAtoms.RateModel`, `BetaLattice` | M | The spectral rate is `β·c0 · (open-mode fraction)`; `β` (persistence hazard) and `c0` (toll) fix the unit. The rate *structure* is complete (bounded, monotone in cutoff, saturating): `betaSpectralRateCutoff_mono`, `betaWeightedRate_univ`, `betaWeightedRate_empty`. Numeric spectral sums / lifetimes are comparison data. |
| E9 | Radiative corrections, hadronic matrix elements | `PMElementaryParticles` B5 | M | `RadiativeCorrection` is a supplied-`R` interface; `BoundStateMatrixElement.value` is supplied. |
| — | External anchors | `PMFlavor`, `PMConstants` | M | `m_e`, absolute wall-mass scale, `α_G` normalization, Planck scale — the dimensionful unit. Isolated in `VevDownstream`, `WallImpedanceChoice`. |
| — | Postulates | `SCOPE.md` | P | Born rule; Lorentzian signature; origin of ℂ. Signature = "volume element squares to −1" (`Derived.SignaturePostulate`). |

## P4 — out of scope

| Item | Note |
| --- | --- |
| General quantum Yang–Mills (transfer matrix, infinite volume, full O(4) restoration, renormalized continuum, mass gap) | See the Yang–Mills scope note in `PMAction/OVERVIEW.md`; the finite-volume OS core is built. |
| Full gravity (metric, Einstein eq., diffeomorphisms) | Weak-field only (`PM-2 WeakField`). |
| Inflation / primordial spectrum | Source free (`Modes.amplitude_free`, `power_free`). |
| Grand unification, electroweak hierarchy/naturalness, CPT | Not addressed beyond a value. |

---

## Selection-symmetry sweep — remaining open verdicts

For each remaining *choice*, the test (`SelectionSymmetry`) is: is it the unique minimizer of a
cost over an explicit option family? The choices that are **open** (not selectable) are:

| choice | symmetry | cost | verdict |
| --- | --- | --- | --- |
| CP-sign branch | continuous phase conj. | provably ties | **M — no-go** (`conjugate_cost_tie`) |
| strong-CP `θ̄` | continuous reference | provably ties | **M** (`ReferenceSelection.invariant_cost_tie`) |
| dark-ratio reading `31/6` vs `25/6` | — (they differ by the baryon unit: `Scaling.disjoint_dark_count_check`, `darkRatio = 1 + 25/6`) | none | **M — reading convention** |
| generation pair-type assignment | discrete `S₃` | generation-blind (`GenerationVacuumChoice`, degenerate before a breaking law) | **M — label** |
| wall anchor `δ` | continuous magnitude | no cost in `δ` | **M** |
| nuclear shell / α / pairing assignments | discrete channel labels | no cost yet | **M** |
| gauge-work price scale | — | min over typed repairs (partial) | **M** — input (`TypedRepairWork`, `ControllerIdentification.gaugeController`) |

**Verdict.** Every open choice is either genuinely **continuous** (so never selectable by a
symmetric cost — a proven no-go: CP sign, `θ̄`), or has **no option family / cost yet** (so a
model input until one is supplied). Supplying the *missing cost functional* is the real lever
for the latter.

## Resolution playbook (by kind)

- **H with a discrete symmetry** → pose the option family and cost; apply
  `SelectionSymmetry.unique_minimizer_fixed`. If it ties, downgrade to **M**.
- **H with a continuous symmetry** → it *cannot* be selected; it is a
  symmetry-breaking input (**M**) — record the orientation choice explicitly.
- **P** → write the premise into the module docstring as a named postulate and stop
  calling it derived.
- **C** → build the object; the tree usually already proves the *obstruction* or the
  *interface*, so the build is bounded.
- **M** → isolate into `tools/e8p/E8PConstants/Experimental.lean` (or the module's
  comparison leaf), never the theorem tree.
- **X** → one scope note; do not reopen.

---

## Cross-cutting tools noted from the Yang–Mills gap branch

(The `PMAction` gap work — `DefectGap`, `GapStability` — is a *partial* attack on the P4 mass gap.
These ideas are reusable on other open items.)

- **Discreteness ⇒ volume-uniform gap.** An **integer-valued** cost with a **unique** ground state
  (up to relabeling) is gapped by at least one unit, *uniformly in volume*, and the diagonal
  transfer contracts the excited sector (`DefectGap.cost_ge_one`,
  `transfer_contracts_excitations`); the gap survives a form-bounded perturbation with `ε < m/2`
  (`GapStability.gap_pos`, `DefectGap.gap_survives_offdiagonal`). The same "discrete count +
  unique minimizer" shape appears in the framework's selection results
  (`SelectionSymmetry.unique_minimizer_fixed`, `Vacuum.least_rank_most_persistent`, E6's
  `probability_uniform_of_const_weight`) — worth reusing wherever an input is a count.
- **Complementary gap halves.** `DefectGap` (diagonal cost) and the pre-existing linearized
  Hessian/Schur gap (`SplitGap`, `VacuumSchur`, `VacuumLocalGap`, `JointVacuumGap`,
  `CompactSplitGap`) are the two halves of a transfer-matrix gap; the open condition joining them
  is a **volume-uniform bound on the off-diagonal form `ε`** (extensive for a lattice gauge
  transfer matrix). See the `PMAction/OVERVIEW.md` Yang–Mills scope note.
- **Gap = coupling; local defects cost locally.** At `p = exp(−β)` the survival weight is the
  Gibbs density `exp(−β·cost)` (`DefectGap.survival_eq_gibbs`, `gap_eq_coupling`), so the per-tick
  gap *is* the Gibbs coupling — a general "decay rate = coupling" reading. And a defect confined to
  a region `Λ` has cost bounded by the adjacent pairs touching `Λ` (`cost_le_of_defect_subset`),
  the first step of a locality argument for the off-diagonal part.
