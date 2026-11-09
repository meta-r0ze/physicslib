# OPEN-PROBLEMS — the consolidated register of what is not yet derived

The Lean tree is the ground truth for what is *checked*. [`SCOPE.md`](SCOPE.md) is the
coarse coverage map; each module's `REVIEW-AND-NEXT.md` lists that module's residues.
**This file consolidates every residue into one prioritized register**, and for each
records *why a reader flags it*, *what the E8 substrate / persistence would have to
produce* to close it, and *the quickest test*.

The results already match experiment; a critic will not dispute those. They will
flag the **load-bearing premises** — the items below whose resolution changes whether
the main claims are *derived* or *conditional*. Resolve those first.

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

## Priority

- **P0** — load-bearing: unresolved, the headline claims stay conditional.
- **P1** — foundational: anchors and constructions the derivations run on.
- **P2** — derivable leaves: concrete theorems/builds, ready to do.
- **P3** — model-input leaves: data or selected laws; state once.
- **P4** — out of scope.

## Current state (one glance)

Everything below is *closed, characterized as a postulate/input, or a named frontier*. The
substantive **open** items are exactly:

- **S5** — **closed.** The constants layer *defines* `α := causalCoupling = 1/Z_geo`, so `α⁻¹ = Z_geo`
  is a theorem; the response form `4π/g²(0) = Z_geo` is just `g² = 4πα`
  (`matching_frontier_iff_admittance`) — equivalently the electric calibration the tree already
  assumes (`matching_frontier_iff_calibration`), and the workload is the substrate's own electric
  ledger (`footprint_eq_electric_ledger`). **No separate dynamical residual:** the physical content
  is the identification `α = κ`, tested numerically (`Z_geo ≈ α⁻¹`, certified, compared in e8p).
- **A1 / A3** — the two-body delta-function / energy-shell reduction (A1) and the three-body
  factorization (A3). No longer Mathlib-blocked: the `ℝ³` spherical change of variables is now
  constructed (`PolarMeasure.integral_radial_three`, using Mathlib's `integral_fun_norm_addHaar`),
  which is A2; A1/A3 are now ordinary proofs. The finite E8 route (`BetaLattice`/`LeptonLattice`)
  bypasses them for the rates.

Everything else is **closed** (S2, S3, R1, E6, K2, K3, K5, A6, R5, measurement+entanglement),
**resolved as a postulate** (S1→Postulate L, S4, signature, Born rule, ℂ), **a proved obstruction /
selection** (R3, K1), or a **labelled input** (P3). Items removed as not-open: A4, A8 (dead
scaffold / tool convenience — see below).

### Removed after review — not open problems

- **A4 (spectral asymptotic `uniformResponse n/n⁵ → 1/(16π)`)** — *dead scaffold.* `cubeLapN`, `spectralGreen`, `uniformResponse` were referenced by **nothing** in the tree; the `1/(16π)` "target" was a numerical observation (`S(3)=743/51,…`) promoted to a goal. The papers never state it. Deleted: `LatticeSpectral` trimmed to the one consumed object (`dirichletEigenvalue`, used by `BetaLattice`); the scaffold modules `LatticeSpectralGreen/Mode/Uniform/Asymptotic` removed.
- **A8 (`certifiedMass` rational enclosure)** — *tool convenience.* The e8p periodic table prints its own rational `boundWeightU` and never imports `certifiedMass`; no paper asserts the enclosure. The added bound lemmas were reverted.

> **Naming note.** The paper's `A₄`/`A₈` are *lattice candidates* in the substrate selection — `Sectors.sector_selection` dismisses `A₄` (glue `ℤ/5`) and keeps `D₄`; `E8Unique.e8_unique`/`Vacuum.geometric_selects_e8` give `E₈`. Those are **kept** (the load-bearing E8-selection) and are unrelated to the removed `A4`/`A8` register IDs.

---

## P0 — load-bearing (a reader flags these first)

| ID | Item | Modules | Kind | What E8 / persistence must produce | Quick test |
| --- | --- | --- | --- | --- | --- |
| S1 | **Persistence → lattice.** Why an additive discrete address structure + integral quadratic cost. | `PMSubstrate/Address.lean` + `Vacuum` | **resolved — Postulate L** | The address structure is `Address.integer_coordinates` (finitely generated + torsion-free additive group ⇒ `ℤⁿ`); the integral quadratic cost is `Address.integer_gram_representation` (integer symmetric bilinear cost ⇒ integral Gram `A`); Finiteness gives `A.PosDef` (`Address.finite_budget_gram`). So the lattice + quadratic cost are *consequences* of the algebraic address/cost premises — promoted from `Research` to the main path. | **Derived**; remaining inputs are the premises themselves (additive group, finite generation, torsion-free, bilinear integer cost), which `Research/ConstraintFoundations` shows bare persistence does not force. **Witness:** `Address.finsupp_not_finite_generated` — `ℤ^{(∞)}` has finite cost sublevels but is not finitely generated, so Finiteness alone fails; the load-bearing extra premise is bit-addressing (`2Λ* ⊆ Λ`). **Resolved (negatively):** bit-addressing does *not* force f.g. — the infinite-rank even lattice `D_∞ = {x ∈ ℤ^(∞) : Σxᵢ even}` (`Address.DInf`) satisfies bit-addressing (`Address.two_smul_mem_DInf`) and finite levels yet is not f.g. (`Address.DInf_not_finite`). So the f.g. of Postulate L is a **genuine additional premise**. |
| S2 | **Conservation → θ symmetries.** Why the state enumeration carries the T / S modular laws. | `PMSubstrate` (`Vacuum`, `Translation`, `RankEight`) | **closed** | The state enumeration is its theta series; both laws are *equivalent* to algebraic properties the postulates already force: **T** ⟺ evenness (`Translation.even_iff_T_invariant`, Protocol/orthogonal exchange) and **S** ⟺ unimodularity (`Translation.unimodular_iff_S_covariant`, Map/Closure/self-readability). `Vacuum.state_sum_T` / `state_sum_S` expose the chain. | **Closed:** the T and S laws are not extra inputs — they are Conservation/Closure rewritten. |
| S3 | **Persistence → minimum rank.** | `PMSubstrate` (`Vacuum`, `RankEight`, `E8Unique`) | **closed (mechanism)** | Even unimodular lattices by rank; rank 8 forced (`E8Unique.e8_unique`). Economy follows from the **hazard form**: one currency + no memory (`PersistenceMechanics.HazardForm`) make period survival a positive multiplicative function `F` of the register count, hence `F n = p ^ n` (`Vacuum.survival_geometric`) with `p = F 1 ∈ (0,1)` when the per-register cost is positive (`exp_survival_unit`). `p ^ n` strictly decreases in rank (`survival_dilutes`), and `economy_from_hazard` reproduces `Economical` (rank ≥ 8 by `geometric_rank`, `e8` attains). Volume-economy is degenerate (`geometric_det_one`). | **Closed:** `economy_from_hazard` + `survival_geometric` + `exp_survival_unit`. The per-register cost is positive by the unit-toll premise (`NetCost`). Remaining: nothing structural — only the HazardForm premises themselves (already listed). |
| S4 | **E8 → clock / sectors / costs.** Why the vacuum *uses* the E8 clock, sectors, events, weights, saturation. | `PMSubstrate` (`Clock`, `Sectors`, `NetCost`) | H | Δ = 43 = order of the discriminant group; ν = 16 spinor channels; σ = 5, χ = 2 from the least boundary. Forced **given** the postulates (`persistence_selects`); missing: the postulates themselves. | `VacuumIndependence` already gives per-postulate counterexamples — the substrate set is minimal/independent. |
| S5 | **Geometric index → EM response.** | `PMSubstrate.PhysicalBridge`, `PMConstants.ResponseMatching` | **closed — matching is a definition/calibration** | The response is **computed** (`irResponse_eq`, `GaugeFluctuation.quad_eq_hess`, `GaugeGroupFactor.canonical_iff`). The matching is **not an extra hypothesis**: the constants layer *defines* `α := causalCoupling = 1/Z_geo` (`CertifiedConstants.α`), so `α⁻¹ = Z_geo` is a theorem and the impedance form `4π/g²(0) = Z_geo` is the rationalized-units normalization `g² = 4πα` (`matching_frontier_iff_admittance`). Equivalently it is the electric calibration the tree already assumes (`matching_frontier_iff_calibration`, the premise of `EventStiffness.calibration`), and it *determines* the event product `toll·m·W = Z_geo/(4π)` (`matching_frontier_iff_event_product`). | Response computed; matching = definition/calibration. The workload is the substrate's electric ledger (`footprint_eq_electric_ledger`). **No separate dynamical residual:** the content is the identification `α = κ`, tested numerically (`Z_geo ≈ α⁻¹`, certified, compared in e8p). |
| R1 | **Physical state space + readout contract.** The complex-amplitude/coordinate readout and carrier allocation. | `PMAction.Machine.CarrierClassBundle`, `CarrierParity` | **contract constructed** | The readout **is built**: `CarrierClassBundle.isometry` (24 observed modes sit losslessly in 48 native labels), `generator_observed` + `evolution_readout` (no hidden-mode feedback), `CarrierParity.range_iff_odd`/`projector` (the observed sector is *intrinsically* the antipodal-odd sector), `carrier_exchange_parity` (fermionic statistics). `readout_contract` packages it. **Input**: admitting this readout as physical (modelling boundary) and admitting the three classes simultaneously (generation content). | **Contract constructed**; the admission is the input, not a missing theorem. |
| E6 | **Measure + normalization.** Counting measure, continuum density `1/(32π²)`, electron measure, parent flux, overall normalization. | `PersistenceMechanics.ChannelMeasure`, `PMElementaryParticles` B2 | **H — selection done** | The **counting measure is persistence-selected**: equal weights give `ChannelMeasure.probability = LawSelection.uniform`, the unique minimizer of the long-run rate (`probability_uniform_of_const_weight`, `LawSelection.averageRate_eq_iff`), and Closure forces it (`probability_perm_uniform`). Spectral weights are the E8 template (`PMAtoms.SpectralMeasure.betaChannelMeasure`). **Input**: the continuum normalization / which modes and their weights. | **Selection closed** (`probability_uniform_of_const_weight`); normalization is the readout input. |
| K2 | **Weak-fraction normalization.** Effective vs raw ledgers; which reference cell is reserved. | `PMConstants.SharedReference`, `ReferenceFrames` | **resolved** | The premise is **derived**: maximal payload reserves exactly one cell (`SharedReference.reserved_single`), the two electroweak refreshes must share a reference type (`SharedReference.shared`), and it is the lepton doublet (`SharedReference.reference_selected`, the W mass picks L over Q); colour is not reserved (`SharedReference.colour_not_reserved`). So `s = 1849/8295`, not assumed. | Done. |
| K3 | **Strong-coupling normalization.** Charge units; colour reference in the payload. | `PMConstants.SectorObligations`, `ColourReference` | **resolved** | The count is **forced**: an exact refresh of the twelve coloured channels needs at least twelve records (`SectorObligations.colour_needs_twelve_reads`, `12 ≤ R`), the ledger is twelve payload reads (`SectorObligations.colour_cost`), and the reference lies in the payload (`ColourReference.colour_reference_in_payload`). | Done. |

## P1 — foundational anchors and constructions

| ID | Item | Modules | Kind | What must be produced | Quick test |
| --- | --- | --- | --- | --- | --- |
| R3 | **Prepared initial reference.** Closed basis-preserving controls cannot supply it. | `PMAction.Machine.PrimitiveRecordBoundary` | **C — obstruction proved** | The impossibility is a theorem: no basis-preserving gate produces the required two-support state (`PrimitiveRecordBoundary.cannot_prepare`). The *supplier* — a preparation/source contract — is the input (a modelling boundary). | Proved; supplier is input. |
| K1 | **Gauge work / price scale.** | `PMConstants.ControllerIdentification` | **H — selection done** | Minimal-cost repair is supplied and selected: `gaugeController` (`weakWitness`) is admissible, has cost `21`, and reproduces `clockRatio` (`gaugeController_cost`, `gaugeController_admissible`, `gaugeController_mixing`). The *overall price scale* is the input. | Selection done; price scale is input. |
| K5 | **Scalar λ budget dynamics.** `c > 0` optimum strictly below `128/989`. | `PMConstants.PersistentGain` | **resolved** | Maximal gain fails for every `c > 0` (`PersistentGain.maximal_not_persistent`); there is a unique largest persistent gain `g*`, strictly between the matched gain and `128/989`, with the explicit bound `128/989 − g* < c·10⁻⁸/23` (`persistent_maximum`). So the physical optimum is pinned below the naive maximal value. | Done. |
| A1–A3 | **Continuum phase space.** Two-body measure, radial shell, three-body factorization. | `PMElementaryParticles` (`PhaseSpace`, `PolarMeasure`, `ContinuumPair`, `MassiveDaughterSpectrum`) | **H — A2 done; A1/A3 open (now unblocked)** | **A2 constructed**: the `ℝ³` spherical change of variables `∫_{ℝ³} g(‖p‖) = 4π∫₀^∞ r² g(r) dr` is `PolarMeasure.integral_radial_three`, from Mathlib's polar decomposition (`MeasureTheory.integral_fun_norm_addHaar`), with the genuine `S²` measure (`sphere_area_three`, `volume.toSphere`) and unit-ball volume (`volume_ball_three`); the massless measure follows (`electron_measure_from_integral`). So the earlier "blocked on Mathlib (no spherical-coordinate integral)" is **stale** — Mathlib has it. Remaining: A1's delta-function / energy-shell reduction and A3's three-body factorization (both now doable). | **A2 done** (real spherical measure); A1/A3 unblocked. |
| — | **External anchors.** `m_e`, absolute wall-mass scale, `α_G` normalization, Planck scale. | `PMFlavor`, `PMConstants` | M | Nothing to derive: the dimensionful unit. State once. | Already isolated (`VevDownstream`, `WallImpedanceChoice`). |
| — | **Postulates.** Born rule; Lorentzian signature; origin of ℂ. | `SCOPE.md` | P | Nothing derivable; state once. Signature = "volume element squares to −1" (`Derived.SignaturePostulate`). | Confirm the tree already labels these as postulates in-module. |
| — | **Measurement, basis selection, entanglement.** | `PMAction.Measurement` | **C — joint space + Born rule constructed** | The von Neumann premeasurement is built: a joint state space (`Joint N`), the controlled **unitary** interaction (`interaction`, `normSq_measure`), the **entangling** post-state (`measure_prepare`: `Σ_i ψ_i |i⟩⟨i|`), and the pointer readout, from which the **Born rule follows** (`born`: `P(j)=‖ψ_j‖²`; `born_total`: outcomes sum to the state norm). So basis selection/probabilities are *derived*, not postulated. **Remaining:** identifying the substrate's own readout with this apparatus (modelling boundary) and multi-system entanglement. | Constructed (single apparatus). |

## P2 — derivable now (concrete theorems / builds)

| ID | Item | Modules | Kind | Test |
| --- | --- | --- | --- | --- |
| R5 | **OS quotient / physical Hilbert space.** Hermitian semi-inner-product + Cauchy–Schwarz; null set is a subspace and the kernel `Submodule` `osNullSubmodule`; the Gram matrix `osGram B F` of a finite family is **PSD** (`osGram_posSemidef`), so `osGramInnerProductSpace` makes `n → ℂ` the **physical Hilbert space** (`Matrix.PosSemidef.toInnerProductSpace`). | `PMAction` §5 | **H — finite-dimensional form done** | Only the infinite/family-free quotient `V ⧸ osNullSubmodule` (for observables not assumed finite) remains; the finite-dimensional Hilbert space is assembled. | **Done** (finite-dimensional): PSD Gram + descended inner product. |
| A6 | **E8 per-channel rate/clock.** The nuclear `MeanLife` layer. | `PMAtoms` §5 (`BetaLattice`) | **H — bounds done** | The spectral rate is bounded by `β c0` (`BetaLattice.betaWeightedRate_le`, `betaSpectralRateCutoff_le`), and the structural `BetaLattice`/`AlphaFinite` chains exist. **Remaining:** the actual numeric spectral sum (comparison data) and the absolute attempt frequency — data, not a theorem. | Bound done. |
| A1d | **Heavy deformation shape (N > 146).** | `PMAtoms` §1 | H/M | Holdout even-even actinides scatter ±0.019 u; candidate ranking done; needs a Z-dependent/mid-shell factor. |
| A5 | **Neutrino decay channel.** No lighter-than-zero channel. | `PMAtoms` §4b | H | `neutrino_stable` is proved; a massive-neutrino channel needs a new mass ledger. |

## P3 — model-input leaves (data / selected laws; state once)

| ID | Item | Modules | Kind | Note |
| --- | --- | --- | --- | --- |
| F1 | Wall anchor magnitude δ | `PMFlavor` | M | Direction/functional form E8; magnitude has no cost functional (`unitWall`, `ckmWall` anchors). |
| F2 | Absolute wall-mass scale | `PMFlavor` | M | Ratios E8 (`capacity_ratio_sq`, `coupling_ratio`); scale external. |
| C1 | Dark ratio `31/6` vs `25/6` | `PMCosmology` (`Scaling`) | M | Both proved distinct; which is `Ω_DM/Ω_b` is recorded as input. |
| A2c | Nuclear charge tail | `PMAtoms` §2 | M/H | 3×3×3 charge response exact; heavy scaling needs a finite-size differential. |
| A3c | Deformed proton closure `2(Δ+σ)=96` | `PMAtoms` §3 | H | Candidate; simple closure overcorrects U-238. |
| A7 | Electron screening/exchange, Aufbau order | `PMAtoms` §6 | M | Fill order is a supplied input (hydrogenic `−R∞/n²` has no ℓ-dependence). |
| C1–C7 | Cosmology Part B | `PMCosmology` | M/C | State/clock/readout, background `L(a)`, primordial source, baryon-changing event, metric/causal structure, entropy normalization, joint test. |
| E7 | **Decay law / physical E8 tick.** | `PMAtoms.E8Tick`, `E8TickUnit` | **H — tick defined** | The E8 tick is the clock period `Δ = 43` (`E8Tick.e8Tick_eq`), and `DecayLaw` gives the consequences of a supplied per-tick cost. The **SI conversion** (`E8TickUnit`) is a comparison input, explicitly not E8-derived. | Tick = 43; SI unit is input. |
| E9 | Radiative corrections, hadronic matrix elements | `PMElementaryParticles` B5 | M | `RadiativeCorrection` is a supplied-`R` interface; `BoundStateMatrixElement.value` is supplied. |

## P4 — out of scope

| Item | Note |
| --- | --- |
| General quantum Yang–Mills (transfer matrix, infinite volume, full O(4) restoration, renormalized continuum, mass gap) | See the Yang–Mills scope note in `PMAction/OVERVIEW.md`; the finite-volume OS core is built. |
| Full gravity (metric, Einstein eq., diffeomorphisms) | Weak-field only (`PM-2 WeakField`). |
| Inflation / primordial spectrum | Source free (`Modes.amplitude_free`, `power_free`). |
| Grand unification, electroweak hierarchy/naturalness, CPT | Not addressed beyond a value. |

---

## Selection-symmetry sweep (quick-test verdicts)

For each remaining *choice*, the test (`SelectionSymmetry`) is: is it the unique minimizer of a
cost over an explicit option family? Verdicts:

| choice | symmetry | cost | verdict |
| --- | --- | --- | --- |
| two D₄ sectors | discrete exchange | invariance-forcing | **H — done** (`SectorExchange.exchange_fixed_of_unique`) |
| μ–τ balance | discrete `Z₂` | invariance-forcing | **H — done** (`ReferenceFlavour.reference_z2_balance`) |
| uniform law | discrete permutation | min-description | **H — done** (`LawSelection.uniform_law`) |
| CP-sign branch | continuous phase conj. | provably ties | **M — no-go** (`conjugate_cost_tie`) |
| strong-CP `θ̄` | continuous reference | provably ties | **M** (`ReferenceSelection.invariant_cost_tie`) |
| dark-ratio reading `31/6` vs `25/6` | — (they differ by the baryon unit: `Scaling.disjoint_dark_count_check`, `darkRatio = 1 + 25/6`) | none | **M — reading convention** |
| generation pair-type assignment | discrete `S₃` | generation-blind (`GenerationVacuumChoice`, degenerate before a breaking law) | **M — label** |
| wall anchor `δ` | continuous magnitude | no cost in `δ` | **M** |
| nuclear shell / α / pairing assignments | discrete channel labels | no cost yet | **M** |
| gauge-work price scale | — | min over typed repairs (partial) | **H/C** (`TypedRepairWork`, `ControllerIdentification.gaugeController`) |

**Verdict of the sweep.** Every remaining discrete choice is either (a) *already resolved* by
`unique_minimizer_fixed` (sector exchange, μ–τ, uniform law), (b) genuinely **continuous** and so
never selectable by a symmetric cost (CP sign, `θ̄`) — a proven no-go, or (c) has **no option
family / cost yet**, hence a model input until one is supplied. There is no remaining case of a
discrete symmetry with a uniqueness-forcing cost left un-applied. Supplying the *missing cost
functional* is therefore the real lever for the (c) items — not another symmetry argument.

## What a reader will flag first — the ten

1. **S1–S4** — *is E8 itself derived, or postulated?* Currently: E8 is forced from
   9 postulates, whose independence is proved (`VacuumIndependence`); the arrows from
   bare persistence to those postulates are the open frontier.
2. **S5** — *is α computed, or matched?* The index is derived and `α` is *defined* as the
   substrate's admittance, so the matching is a theorem; the physical residual is the
   identification `α = κ`.
3. **R1 + E6** — *what is a particle, and why this measure?*
4. **K2/K3** — *are the normalizations derived or calibrated?* The effective/raw
   ledger split is proved; the reserved-cell premise is the input.
5. **External anchors** — *is the absolute scale predicted?* No; state once.

## Suggested order of attack

1. **S1 → S3** (family + cost from persistence; the substrate's central claim).
2. **S5** (the α bridge; makes "derived, then compared" literal).
3. **R1 + E6** (state space + measure; unblocks PMElementaryParticles Part B).
4. **R5** (OS quotient; finish the one PM-specific QYM step).
5. **A4 / A8** (small derived leaves; quick wins).

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
