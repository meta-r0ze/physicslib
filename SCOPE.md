# SCOPE — the open physics frontier

The Lean tree is the ground truth for what is *checked*; each module's
`TODO.md` lists that module's residues. This file is the cross-cutting map
of the **open physics questions** — where the papers discuss them (cloned under the
sibling `PM/`, `PM-1-Arch/`, … repositories), what the tree covers, and whether the
item is a postulate, scoped out, a conditional relation, or a missing construction.
Update it when a frontier closes.

For the premises, inputs and open physics a reader should know about, see the
per-module `TODO.md` files; each folder's `TODO.md` has the working list.

## The model in one line
One finite E8 substrate + persistence (survival / hazard / selection). E8 values are
derived, then compared to SM values by `tools/e8p`.

## Coverage map

| Question | Papers | Tree status | Kind |
| --- | --- | --- | --- |
| Born rule (probability from amplitudes) | PM-2 `3_appendix_qm_fundamentals.tex` — "no Born-rule theorem … claimed"; `PMElementaryParticles.InclusiveMixing`, `PMKAutomaton.Machine.InterferenceReadout` | open | **postulate** |
| Measurement, basis selection, collapse | PM-2 `3_appendix_qm_fundamentals.tex` §Measurement; `PMAction.Measurement` | **built**: joint `⊗` space + controlled unitary interaction + pointer readout, and the **Born rule derived** (`born`); paper says the rule "can be stated once an observable, probability law and apparatus interaction are supplied" — now supplied | **construction done** (capacity-exhaustion / log2 preferred-basis still open) |
| Entanglement / Bell / no-signalling | PM-2 `3_appendix_qm_fundamentals.tex` §Correlations; `PMAction.Entanglement` | **partial**: two-system joint space, the Bell singlet, perfect correlation and entanglement (`singlet_not_product`) — the paper's "joint state space" need. **Built**: joint space, Bell singlet, perfect correlation, entanglement, and **no-signalling** (`no_signalling_singlet`: the singlet's marginal is `1/2` for a `Z` or `X` distant measurement). **Built**: joint space, Bell singlet, perfect correlation, entanglement, no-signalling, **and the CHSH inequality** (`chsh_eq`: the singlet's CHSH combination is `2√2`; `chsh_violates`: `2 < |CHSH|`, exceeding the local bound) | **constructed** |
| Lorentzian signature `(+,−,−,−)` | PM-1 `DerivedParameters.signature_witness`, `CliffordSignature` | postulated, not derived | **postulate** |
| Lorentz invariance / violation bounds | PM-1 `1_appendix_geometric_origins…`, PM-2 `2_entropic_action`; `PMElementaryParticles.PairIsotropy` ("Lorentz covariance … not asserted") | **partial**: `PMAction.D4Isotropy` proves the link directions (D4 roots / 24-cell) match a rotation-invariant distribution through **degree 4** (`quartic_isotropic`), so the leading *anisotropic* correction is degree 6 (O(a⁴)); the hypercubic alternative fails already at O(a²) (`hypercubic_not_isotropic`) and is excluded. **Open**: a full gauge-action correction formula and O(4) restoration in the continuum limit (the file flags both) | **partly built; continuum O(4) restoration open** |
| Quantum Yang–Mills | PM-2; PM-3 `4_D_temporal_allocation`, PM-5 `7_composites` | **mostly built**: finite-volume Euclidean Gibbs measure (`LatticeGibbs`), gauge invariance (`GeometricGauge.gibbs_preserving`), site-reflection positivity (`ReciprocalReflection.reflection_positive`), classical continuum limit (`LatticeSiteAction`), finite OS core (`Reconstruction`), volume-uniform gap of the diagonal PM cost with perturbative stability (`DefectGap`, `GapStability`), and a volume-uniform mass gap of the distinction substrate (`MassGap.SlabGap.slab_gap_explicit`, `CubicBox.box_mass_gap`; flip-even sector). **Open**: the Osterwalder–Schrader reconstruction from reflection positivity (transfer matrix / Hilbert space), infinite volume, renormalized continuum, mass gap of the gauge layer (a separate continuous field, `NativePacketRouting.pure_permutation_refinement_trivial`; its gap is the general QYM problem) | **partly done; the general-QYM remainder out of scope** (AGENTS) |
| Cosmological constant / vacuum energy | PM-6 `5_dark_sector.tex`, PM-3 `6_geometric_depth`; `PMCosmology.Thermodynamics`, `Hypotheses` | conditional relations only | **model input** |
| Dark matter / dark energy (nature, dynamics) | PM-6 `5_dark_sector.tex`, PM-2 `7_tol_mar_spactime`; `PMCosmology.Scaling.darkRatio = 31/6` | count only, no dynamics | **model input** |
| Inflation / primordial spectrum / initial state | PM-6 `Modes` (`amplitude_free`, `power_free`), `Primordial` | open (source free) | **model input** |
| Full gravity (metric, Einstein eq., diffeomorphisms) | PM-2 `WeakField` (weak-field only), PM-6 `SubstrateLoad` | open | **missing construction** |
| Electroweak hierarchy / naturalness | PM-1/PM-3 (Higgs from `2λv²`) | not addressed (only the value) | **open** |
| Grand unification | PM-3 (a GUT-scale number only) | no group/dynamics | **open** |
| CPT | PM-2 `CPPhases` (T only) | not a theorem | **open** |
| Origin of the complex structure (why ℂ amplitudes) | PM-2 amplitudes | model choice | **postulate** |
| Electromagnetic matching `α⁻¹(0) = Z_geo` | PM-1 `7_correspondences.tex` §EM matching; `PMConstants.ResponseMatching` | **closed**: the constants layer *defines* `α` as the substrate's admittance (`CertifiedConstants.α := causalCoupling`), so `α⁻¹ = Z_geo` is a theorem and the impedance form is the rationalized-units normalization `g² = 4πα` (`matching_frontier_iff_admittance`); equivalently the electric calibration (`matching_frontier_iff_calibration`) at the electric ledger workload (`footprint_eq_electric_ledger`) | **closed**; content = the identification `α = κ`, tested in e8p |

## Named premises

These are identification or modelling premises, not theorem hypotheses hidden in
the text. Each appears once here; the owning TODO links back to this table.

| Premise | Where it enters in Lean | What depends on it |
| --- | --- | --- |
| One receiver tick is one root event | `PMKAutomaton.ClockSites.site`, `arrivals_are_lattice_steps`; `PMKAutomaton.RingReceiver.tick` | EP line and ring traces, registration-count readings, particle-trace schedules |
| Closure: a substrate-defined weight is invariant under the substrate symmetries that fix the clock | `PMKAutomaton.ClockTickWeights.forward_one_orbit`, `backward_one_orbit`; `PMKAutomaton.Machine.SliceHop.silent_words_eq_orbit`, `slice_uniform` | Equal weights of the six forward and six backward tick steps; tick-word costs |
| The aligned spacetime `D4` has one clock-axis step equal to one E8 clock tick | `PMKAutomaton.ClockAlignment.a` … `beta`, `clockAxisRoots_counts`; explicit placement `PMKAutomaton.AlignedSectors.alignedSectorBasis`, `aligned_d4d4`, `alignedSectorBasis_eq`; `ClockEps.rootE8_clock`, `AxisHop.two_epsAxis_reads`, `SliceHop.clock_words_signs` | Replacing `sectorBasis`; clock-routed hop words; the aligned placement recheck |
| Tier assignments `{0,2,3}` for up and `{0,1,2}` for down, electron and neutrino | `PMElementaryParticles.TierLedger.tiersFor`, `QuarkMasses`, `LeptonMasses` | Species mass ledgers, tier descent, decay channel tiers |
| The mass reading of the full-ring spectrum is a hypothesis | `PMKAutomaton.ClockRing`, `Dispersion`; EP mass reading | Identifying the spectral block with a particle mass; the band gap is `x`, the mass-like term `x/2` |
| Lorentzian signature `(+,−,−,−)` and complex amplitudes | `SCOPE` coverage; `PMAction` amplitude and continuum modules | Continuum limits, unitary amplitudes, comparison phases |
| The EP protocol serial route and its admitted schedule | `PMElementaryParticles.WireSchedule.Premises` | Elapsed and paid route costs, writer traffic, scheduled readout |
| The heavy branch reads the supplied record and bank | `PMAction.HeavyFlipControl`, `ElectricCompanionBank`, `ElectricChiralKick` | Heavy label branch, writer population, companion crossing |
| The booked writer population and reset account | `PMAction.WireReferenceCost`, `PMKAutomaton.Values` thresholds | Reference thresholds, erasure versus balanced-reset accounts |
| The lightest charged offset and admitted matched ports | `PMAction.ChargedInsertion.det_flip_at_resonance`, `ResonanceLift` | Charged mass ordering, lightest ratio, selector comparison counts |
| The physical species association for decay and current readout | EP decay theorems, `ExternalStates`; `PMAction.NativeExternal` | Particle identification, decay channels and external-state readout |
| The three persistence premises of `HazardForm` | `PersistenceMechanics.HazardForm`; `PMElementaryParticles.MeanLife` | Mean life, survival weights, lifetime comparisons |
| Strong-CP and VEV structural premises | `PMConstants.VevPremises`, `StrongLedgerBounds`; `UnitTransferWitness` | Constant normalization, strong-CP selection, unit-transfer comparison |
| The machine inputs `T,L,B,D,J,Q` and the tariff unit | `PMKAutomaton.Interface` conditional exports | Physical admission, booked work, detector support, supply and acceptance |
| The cosmological load/response/continuity premises | `PMCosmology.Hypotheses.CosmoModel` | `H_late`, `S8_late`, background and composition comparisons |
| The three carrier premises: both sectors carried to the vector class by triality, the sign as the doublet index, and the reserved (lepton) axis | `PMConstants.CarrierRepresentation` (`charges_from_carriers`, `carrierCharges_eq_standard`) | The channel charge table, the channel types and multiplicities, every downstream charge |
| The representation content: one generation with a sterile singlet | `PMConstants.Hypercharge`, `RequirementTable` | The sixteen-channel inventory and its ledgers |
| The SU(2) and SU(3) subgroups of the packet action, and their normalization | `PMConstants.PacketGaugeActions` | Weak and colour actions on the packet, gauge ledgers |
| The link transport form `θ = (g/2)W·σ + (g′/2)B` with unit hypercharge | `PMConstants.LinkMass` | W and Z masses from the inter-sector link |
| The flavour aperture and forward-composition premises | `PMFlavor.HalfTurnAperture`, `PMFlavor.TransferAmplitude`, `PMFlavor.ConductionRule` | `s12`, `s13`, `|V_cb|` candidates and the completion-order choice |

Two former rows are now derived. `PMElementaryParticles.ChannelPlacement.channelE8`
places the sixteen channels in the aligned internal D4. Its class table and
`referenceClass_eq_clock` identify library class `0` with the clock-carrying
vector coset, so the reference-class identification is a consequence of the
library conventions rather than a premise.

## How each kind is closed
- **postulate** — state it once and stop calling it derived; the tree already flags
  Born rule / signature this way inside modules.
- **out of scope** — state once, as the Yang–Mills note does in `AGENTS.md`.
- **conditional relation** — derive the "if input X then output Y" (already done for
  the VEV, the interface correction, the cosmo rescaling; more is listed in the
  module `TODO` files).
- **missing construction** — build the object (joint state space, metric dynamics).

## Where the choices can be eliminated
`PersistenceMechanics/SelectionSymmetry.lean` gives the test: a model choice is
*derivable* iff the relevant symmetry is **discrete** and its cost forces a **unique
minimizer** (`unique_minimizer_fixed`). Discrete examples that close this way:
sector exchange (`SectorExchange`), the μ–τ balance
(`ReferenceFlavour.reference_z2_balance`), the uniform law (`LawSelection`).
Continuous symmetries (the CP-sign phase conjugation,
`ReferenceSelection.invariant_cost_tie`) provably tie and need a symmetry-breaking
input.
