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
| R1 | **Readout admission.** Admitting the coordinate readout as physical. | `PMAction.Machine.CarrierClassBundle`, `CarrierParity` | **P** | The readout is **constructed and pinned**: `readout_contract` (isometry + native generator observed as the coordinate generator + no hidden-mode feedback `evolution_readout`), and `CarrierParity.projector` fixes the observed 4-mode sector *intrinsically* as the antipodal-odd sector of the 8 carrier labels (no choice of subspace). So nothing of the readout is left to derive; the residual is the single **modelling admission** that the physical readout is this coordinate observation (and that all three glue classes are used) — irreducible, like the Born-rule / apparatus admission, not a missing theorem. | A postulate; state once. |
| E6 | **Measure normalization.** Continuum density, electron measure, `2E` normalization. | `PersistenceMechanics.ChannelMeasure`, `PMElementaryParticles` (`PolarMeasure`, `MuonRate`) | **M** | The counting measure is persistence-selected (`probability_uniform_of_const_weight`, `probability_perm_uniform`); the continuum density `1/(32π²)` factors as `(1/4π)·Φ₂` (`continuum_angular_density`); the electron measure is derived (`electron_measure_from_integral`, `massless_lorentz_measure`); and the **`2E` normalization is derived** — `massShell_reduction` shows it is the `δ(p²−s)` mass-shell reduction Jacobian `2√s`, the same chain-rule shape as A1's `1/2` (so `d³p/((2π)³ 2E)` and the flux `1/(2m)` are not separate inputs). The spectral modes/weights are the E8 `BetaLattice` template. | Only the physical readout normalization (which E8 modes/weights) remains. |
| R3 | **Prepared initial reference.** | `PMAction.Machine.PrimitiveRecordBoundary`, `WalkReferenceCoupling` | **M** | The **supplier is constructed**: `WalkReferenceCoupling.preparation` is a concrete E8-root rotation `LocalUnitary.rotation beta (π/4)`, unitary (`preparation_unitary`) and preparing the reference (`prepares_forward`, `beta_target : preparation *ᵥ seed = quarterState 0 2`). The obstruction `cannot_prepare` / `no_primitive_preparation` is only against the *basis-preserving* `Gate` library (permutations + diagonal phases) — so the pulse is genuinely outside it. Residual: the **seed supply** and the pulse **price/tariff** (a modelling input), not the supplier. | Supplier built; seed + tariff are the input. |

## P2 — open derivable leaves

| ID | Item | Modules | Kind | What is open | Quick test |
| --- | --- | --- | --- | --- | --- |
| A1d | **Heavy deformation shape (N > 146).** | `PMAtoms` §1 | H/M | Holdout even-even actinides scatter ±0.019 u; needs a Z-dependent/mid-shell factor. | Candidate ranking done; shape not yet predictive. |
| A2c | **Nuclear charge tail.** | `PMAtoms` §2 | M/H | The 3×3×3 charge response is exact; heavy scaling needs a finite-size differential. | Low-Z-anchored differential. |
| A3c | **Deformed proton closure `2(Δ+σ)=96`.** | `PMAtoms` §3 | **H** | Candidate; simple closure overcorrects U-238. | Refine the closure. |

## P3 — the input floor (anchors, laws, postulates; state once)

**These are the irreducible inputs, not open derivations.** Each row splits *derived* (in the tree)
from *input* (declared once). The **continuous** ones — a magnitude, a scale, a unit — are *proven
not selectable*: a scale-invariant cost leaves every magnitude tied (`SelectionSymmetry.scale_ties`,
`scale_no_unique_min`); the discrete ones need a cost functional that is not supplied.

| ID | Item | Modules | Kind | Derived / input |
| --- | --- | --- | --- | --- |
| F1 | Wall anchor magnitude δ | `PMFlavor` | M | **Derived:** direction/functional form E8, candidate `ckmWall` (`δ = ε = χ/ν = 1/8`, `ckmWall_delta_eq`). **Input:** the magnitude — a continuous `(δ, ε)` with no cost functional, so not selectable (`scale_no_unique_min`; anchors `unitWall`, `ckmWall`). |
| F2 | Absolute wall-mass scale | `PMFlavor` | M | **Derived:** the ratios (`WallMassRatio.capacity_ratio_sq`, `coupling_ratio`). **Input:** the absolute mass scale (external unit), not selectable (`scale_no_unique_min`). |
| C1 | Dark ratio `31/6` vs `25/6` | `PMCosmology` (`Scaling`) | M | **Derived:** both counts (`darkRatio = 248/48 = 31/6`, `disjoint_dark_count_check`: `31/6 = 1 + 25/6`). **Input:** which is `Ω_DM/Ω_b` — a reading convention (the two differ by the baryon unit); no cost selects it. |
| A7 | Electron screening/exchange, Aufbau order | `PMAtoms` §6 | M | **Derived:** capacities `2n²` and the order's linearisation (`Aufbau.madelungKey`, `aufbau_sorted`). **Input:** the fill *order* (Madelung `(n+ℓ, n)`) — the hydrogenic `−R∞/n²` carries no ℓ-dependence, so it needs screening/chemistry physics; no E8 cost supplied yet. |
| — | Lepton/quark tier-ledger assignment | `PMElementaryParticles.LeptonMasses`, `QuarkMasses` | M | **Derived:** every mass term is a canonical E8 invariant, and the muon's vacuum feedback `(χ+σ)α/(1−α)` is the fixed point of its recursive loop (`muonFeedback_fixpoint`); the cost decompositions are `muon_ledger`/`tau_ledger` and `up_ledger`…`top_ledger`. **Input:** which invariant pays which tier cost (the paper's proposed protocol ledger); no option family/cost functional selects it. (The **hadron** masses are now derived via occupancy — see the row below.) |
| — | Hadron composite occupancy and decay constants | `PMHadrons` (`Occupancy`, `StrangeCarrier`, `NucleonBase`, `TollGovernor`, `Emission`, `EmissionScale`) | M/C | **Derived:** a composite's mass is its occupancy — `n = χ + σ·ℓ` cells (Map base `χ` + Protocol direction register `σ` per line carrier, `StrangeCarrier`) and the nucleon base `Δ²` is Margin's one-cycle causal cone (`NucleonBase`); Toll is the emission boundary (`emissionWeight = tollTerm`) and Governor the cycle persistence (`χ/Δ`); all four meson ledgers are the occupancy form (`meson_ledgers`). **Input:** the **emission mode space** — the decay constants are the VEV over it (`fπ = v/N_π`, uniform persistence-selected configuration, `EmissionScale`), with assigned counts `N_π = Δ²+Δ−χ = 1890` and `N_K = Δ²−ν² = 1593` (perturbations of the causal cone); not identified. Readings tested and failed: GMOR, occupancy-scaling (`occupancy_reading_excluded`), the boundary-event space. |
| C1–C7 | Cosmology Part B | `PMCosmology` | M/C | State/clock/readout, background `L(a)`, primordial source, baryon-changing event, metric/causal structure, entropy normalization, joint test. |
| E7 | Decay law / physical E8 tick | `PMAtoms.E8Tick`, `E8TickUnit` | M | The E8 tick is the clock period `Δ = 43` (`E8Tick.e8Tick_eq`); the **SI conversion** (`e8TickSeconds = 43 · electronSecond`, `E8TickUnit`) is a unit/scale anchor, explicitly not E8-derived and not selectable (`scale_no_unique_min`). |
| — | Nuclear rate unit `β·c0` (absolute attempt frequency) | `PMAtoms.RateModel`, `BetaLattice` | M | The spectral rate is `β·c0 · (open-mode fraction)`; `β` (persistence hazard) and `c0` (toll) fix the unit. The rate *structure* is complete (bounded, monotone in cutoff, saturating): `betaSpectralRateCutoff_mono`, `betaWeightedRate_univ`, `betaWeightedRate_empty`. Numeric spectral sums / lifetimes are comparison data. |
| E9 | Radiative corrections, hadronic matrix elements | `PMElementaryParticles` B5 | M | `RadiativeCorrection` is a supplied-`R` interface; `BoundStateMatrixElement.value` is supplied. |
| — | External anchors | `PMFlavor`, `PMConstants` | M | `m_e`, absolute wall-mass scale, `α_G` normalization, Planck scale — the dimensionful unit. Also the gauge-work **price scale**: it is the toll *unit* (`c₀ = 1` transition, `NetCost`), and the controller selection is scale-free (`ControllerLedger.selection_scale_free`), so it is an anchor, not a selection input. Isolated in `VevDownstream`, `WallImpedanceChoice`. As scales/units they are not selectable (`SelectionSymmetry.scale_no_unique_min`). |
| — | Postulates | `SCOPE.md` | P | Born rule; Lorentzian signature; origin of ℂ. Signature = "volume element squares to −1" (`Derived.SignaturePostulate`). |

## P4 — out of scope

| Item | Note |
| --- | --- |
| General quantum Yang–Mills (transfer matrix, infinite volume, full O(4) restoration, renormalized continuum, mass gap) | See the Yang–Mills scope note in `PMAction/OVERVIEW.md` and `PMAction/MassGap/README.md`; the finite-volume OS core is built. |
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
| wall anchor `δ` | continuous magnitude | scale-invariant ⇒ ties | **M — no-go** (`SelectionSymmetry.scale_no_unique_min`) |
| nuclear shell / α / pairing assignments | discrete channel labels | no cost yet | **M** |
| gauge-work price scale | continuous (`c₀`) | selection is scale-free | **closed** — the least-cost controller is invariant under the toll (`ControllerLedger.selection_scale_free`); the scale is a unit (anchor) |

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
