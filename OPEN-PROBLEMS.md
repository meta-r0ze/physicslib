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

---

## P0 — load-bearing (a reader flags these first)

| ID | Item | Modules | Kind | What E8 / persistence must produce | Quick test |
| --- | --- | --- | --- | --- | --- |
| S1 | **Persistence → lattice.** Why an additive discrete address structure + integral quadratic cost from bare persistence. | `PMSubstrate` (`Vacuum`, `Translation`) | H | The option family of even, unimodular, bit-addressed lattices and a description-length cost; Economy picks least rank (`RankEight.rank_dvd_eight`). Missing: the *arrow* from persistence to that family. | Does any persistence-definable cost have a unique minimizer over the family? (Selection result exists once the family+cost are posed.) |
| S2 | **Conservation → θ symmetries.** Why the state enumeration carries the T / S modular laws. | `PMSubstrate` (`Vacuum`) | H | State space = discriminant group of the clock plane; bijective bit-addressable evolution forces its modular action. Missing: the implication. | Exhibit a bijective-update family whose symmetry group is exactly SL(2,ℤ) on the discriminant group. |
| S3 | **Persistence → minimum rank.** The comparison family, cost, weights, and exclusion of ranks > 8. | `PMSubstrate` (`RankEight`, `E8Unique`, `Vacuum`) | **H — mechanism supplied** | Even unimodular lattices by rank. Rank 8 forced (`E8Unique.e8_unique`); Economy = least rank: (i) all geometric substrates are **unimodular** (`Vacuum.geometric_det_one`), so volume-economy is degenerate and rank is the only nondegenerate parameter; (ii) **independent register survival at `p ∈ (0,1)`** gives period survival `p ^ n` (`Vacuum.survival_dilutes`), maximized at least rank, and `least_rank_most_persistent` plus `geometric_rank` reproduces `Economical` — so the cost is *derived* from a survival mechanism, not postulated. | **Done** (`survival_dilutes`, `least_rank_most_persistent`); independence is `economy_needed`. Remaining: justify independent register survival physically (why `p<1` per register, independent). |
| S4 | **E8 → clock / sectors / costs.** Why the vacuum *uses* the E8 clock, sectors, events, weights, saturation. | `PMSubstrate` (`Clock`, `Sectors`, `NetCost`) | H | Δ = 43 = order of the discriminant group; ν = 16 spinor channels; σ = 5, χ = 2 from the least boundary. Forced **given** the postulates (`persistence_selects`); missing: the postulates themselves. | `VacuumIndependence` already gives per-postulate counterexamples — the substrate set is minimal/independent. |
| S5 | **Geometric index → EM response.** The substrate *computes* the optical response — the local index `n = ν/(ν−K)` = reciprocal clock speed (`PMAction.SpatialResponse.localIndex_eq_inv_clock`); converting it to `α` needs the Maxwell matching coefficient, and `PhysicalBridge.response_leaves_matching_free` proves positivity leaves it free (every `Z, g²` admit some `C`). | `PMSubstrate` (`PhysicalBridge`, `Impedance`) | **H (response) done + M (matching)** | The normalized response — the Maxwell matching law `Z = C/g²` — is a model input; no response computation pins `α` alone (`matching_coefficient`). | Quick test done: `response_leaves_matching_free`. |
| R1 | **Physical state space + readout contract.** The complex-amplitude/coordinate readout and carrier allocation. | `PMAction` §1, `PMElementaryParticles` B1 | C/H | The 16-channel E8 spinor representation as the state space; the carrier class/wall allocation. | Check the 24 minimal carriers vs 48 generation-labelled modes (`GenerationEncoding`, already flags the capacity bound). |
| E6 | **Measure + normalization.** Counting measure, `1/(32π²)`, electron measure, parent flux, overall normalization **derived from the readout**. | `PMElementaryParticles` B2, `PersistenceMechanics.ChannelMeasure` | H | The finite `ChannelMeasure` with E8 spectral weights (`PMAtoms.SpectralMeasure.betaChannelMeasure` is the template). | Does persistence select the counting measure over the option family? (`unique_minimizer_fixed`.) |
| K2 | **Weak-fraction normalization.** Effective vs raw ledgers; which reference cell is reserved. | `PMConstants` (weak row) | H | Premise: *one reserved cell per reference type; both EW refreshes read the reserved reference.* W mass already picks L over Q (`SharedReference.reference_selected`). | Confirm the reserved-cell premise is forced by η = 171/172, or derive it. |
| K3 | **Strong-coupling normalization.** Charge units; colour reference in the payload. | `PMConstants` (strong row) | H | 12·η minimal refresh of the coloured payload (`ColourReference.colour_ledger_minimal`); read scale = Z. | `SectorObligations.colour_needs_twelve_reads` — check the count is forced, not assumed. |

## P1 — foundational anchors and constructions

| ID | Item | Modules | Kind | What must be produced | Quick test |
| --- | --- | --- | --- | --- | --- |
| R3 | **Prepared initial reference.** Closed basis-preserving controls cannot supply it. | `PMAction` §3, `Machine` | C/M | A preparation/source contract (`ReferenceSourceBoundary`, `PrimitiveRecordBoundary.cannot_prepare` prove the obstruction; the supplier is the input). | Already have the impossibility theorem; the test is whether *any* admissible gate prepares it. |
| K1 | **Gauge work / price scale.** Price admissible primitive words; η as work. | `PMConstants` (`TypedRepairWork`, controller) | C/M | Minimum-cost repair pricing (`ControllerIdentification.gaugeController` reproduces `clockRatio` at cost 21); the *overall price scale* is the input. | η ≠ controller cost (`Controller cost does not derive η`): confirm η stays the frame fraction. |
| K5 | **Scalar λ budget dynamics.** c > 0 optimum strictly below 128/989. | `PMConstants` (`ScalarLedger`, `PersistentGain`) | H | Budget 3 = moved directions; maximin gain; N = 23 pinned once B = 3 (`RegulatoryMaximin`). Missing: the physical budget dynamics. | Check whether the c > 0 optimum can be pushed to 128/989 or is bounded strictly below. |
| A1–A3 | **Continuum phase space.** Two-body measure, radial shell, three-body factorization. | `PMElementaryParticles` A1–A3 | H/X | The standard Lorentz-invariant measure, *constructed*. A2 is blocked on Mathlib (no spherical-coordinate integral). **Status:** optional — the finite `BetaLattice`/`LeptonLattice` route bypasses it. | A1 partial (`PhaseSpace.solidAngle_one`); A2 blocked on infrastructure, not on PM. |
| — | **External anchors.** `m_e`, absolute wall-mass scale, `α_G` normalization, Planck scale. | `PMFlavor`, `PMConstants` | M | Nothing to derive: the dimensionful unit. State once. | Already isolated (`VevDownstream`, `WallImpedanceChoice`). |
| — | **Postulates.** Born rule; Lorentzian signature; origin of ℂ. | `SCOPE.md` | P | Nothing derivable; state once. Signature = "volume element squares to −1" (`Derived.SignaturePostulate`). | Confirm the tree already labels these as postulates in-module. |
| — | **Measurement, basis selection, entanglement.** | `SCOPE.md` | C/X | A joint state space + apparatus interaction; no joint space exists yet. | — |

## P2 — derivable now (concrete theorems / builds)

| ID | Item | Modules | Kind | Test |
| --- | --- | --- | --- | --- |
| R5 | **OS quotient / physical Hilbert space.** Hermitian semi-inner-product + Cauchy–Schwarz; null set is a subspace and the kernel `Submodule` `osNullSubmodule`; the Gram matrix `osGram B F` of a finite family is **PSD** (`osGram_posSemidef`), so `osGramInnerProductSpace` makes `n → ℂ` the **physical Hilbert space** (`Matrix.PosSemidef.toInnerProductSpace`). | `PMAction` §5 | **H — finite-dimensional form done** | Only the infinite/family-free quotient `V ⧸ osNullSubmodule` (for observables not assumed finite) remains; the finite-dimensional Hilbert space is assembled. | **Done** (finite-dimensional): PSD Gram + descended inner product. |
| A4 | **Spectral asymptotic** `uniformResponse n / n^5 → 1/(16π)`. | `PMAtoms` §4 | H | A genuine `Tendsto` asymptotic; not needed for the mass ledger. |
| A8 | **`certifiedMass` rational enclosure.** Leading vs certified gap = `binding`. | `PMAtoms` §7, `tools/e8p` | H | Interval arithmetic over the π/√-containing mass; then print the certified column. |
| A6 | **E8 per-channel rate/clock.** The nuclear `MeanLife` layer. | `PMAtoms` §5 | H | `BetaLattice`/`AlphaFinite` structural chains exist; the numerical spectral sum + absolute attempt frequency remain. |
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
| E7 | Decay law / physical E8 tick | `PMElementaryParticles` B3 | M | `DecayLaw` gives consequences of a supplied cost; the tick is the input. |
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
2. **S5** — *is α computed, or matched?* The index is derived; the EM *response*
   normalization is the bridge.
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
