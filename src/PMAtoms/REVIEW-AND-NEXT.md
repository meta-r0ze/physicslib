# PMAtoms — open work

Checked results are in [`OVERVIEW.md`](OVERVIEW.md); the Lean source is the ground truth. This
file lists only what remains, triaged by the **E8 pattern** it uses. Everything here is an E8
statement; measured masses and lifetimes are the comparison, never inputs.

A nucleus is a composite of nucleons (`Nucleus`), exactly as a hadron is a composite of carriers,
and an atom is a composite of a nucleus and its electron cloud. So the same machinery the hadron
level built (`PMHadrons`) applies:

| E8 pattern | hadron level (`PMHadrons`) | this level |
| --- | --- | --- |
| **occupancy** — mass = substrate held | `n = χ + σ·ℓ` cells, `Δ²` cone (`Occupancy`, `NucleonBase`) | the nucleus link ledger `πD`/`σ/2` (`LinkWeights`) and the closure counts (`E8AtomValues`) |
| **emission overlap** — a composite sheds parts | Toll boundary × overlap (`Emission`) | α / fission **fragment overlap** (hindrance) |
| **Governor** — per-slot persistence | `χ/Δ` per slot (`TollGovernor`) | the nuclear **attempt frequency** / per-slot hazard |
| **persistence selection** | `SelectionSymmetry` | **regime / valley** selection |

## 1. Occupancy: the nucleus ledger and closures — H/M

The nucleus mass is the free-nucleon sum minus the link/closure layers (`TwoLedger`,
`NuclearLedger.certifiedMass`), reusing the nucleon terms (`LinkWeights.mapWeight = πD`,
`boundaryWeight = σ/2`) and the E8 closure identities (`E8AtomValues`: `2(Δ−χ)=82`,
`(σ−χ)(Δ−1)=126`, `2(Δ+σ)=96`, `(σ−χ)Δ+(ν+σ+χ)=152`, …).

**Open.** A residual decomposition (`e8p --certified`, `R = certified − m_iso` in `m_e`) gives
three E8 questions, in priority order. `R` splits into a **systematic** light-nucleus over-binding
(`R/A ≈ −2` at Li-7 rising to `≈ −0.03` at Pb-208), a **shell oscillation** (±`5 m_e`, `R ≈ 0` at
the doubly-magic O-16 and the closure-adjacent C-12/Fe-56/Ni-62), and a **frontier** term. None is
a fitted correction; each is a derivation.

1. **General finite-size link/closure count (Q1).** The ledger uses the *continuous*
   `packingLinks(A) = (σ−χ)(A − A^{2/3})`, but `packingLinks_cube` proves it is exact **only at
   cubic `A = n³`** — every other `A` is a mean-field interpolation. Derive the **exact
   finite-complex count for arbitrary `A`** (the general `packingLinks`/`packingClosureRank`, given
   the E8 filling rule). Largest lever: it is the systematic term. Not a special-case patch — the
   cube result is the `A = n³` instance of the general count.
2. **Shell system as a six-pillar E8 system (Q2).** The smooth ledger is blind to the discrete
   closure ladder (`NuclearShells`), so `R` oscillates between shells. `SingleParticle` is a
   *candidate* module whose level energies are schematic (`n + l/10 − j/20`), not E8-derived — a
   schematic Strutinsky does **not** reproduce the oscillation (wrong magnitude and shape). Build
   the shell system out from the pillars, as was done at the atom level: the ladder `2,6,12,8,…`
   is E8; its **spacings and couplings** are not yet. **Progress (`ShellSystem`)**: capacity
   `2j+1`, the oscillator `2n+l` order (Capacity), and the cumulative ladder are proved; the
   `l²`/spin–orbit ratio is **forced to `1/D`** by the order (`l2_ratio_forced`), and the E8
   spacings (`κ=χ/Δ`, `κ₂=κ/D`) reproduce the recorded order (`e8OrbitalOrder`). Only the overall
   scale `κ` is free — it needs an E8 energy scale, not a fit.
3. **(Deferred) Deformed closure / frontier (Q3).** `Cm-244` is under-bound by `+44 m_e` — a
   missing extra binding at the deformed closure `Z=96, N=152`. Localized to the frontier; hold
   until Q1/Q2 land unless it turns out to help the bulk. Subsumes the old items: the
   `2(Δ+σ)=96` term overcorrects U-238, and the `−43/288` deformation candidate fails its holdout.

**Built (`NuclearOccupancy`).** The occupancy `A = Z + N`, the closure predicates
(`ProtonClosed`/`NeutronClosed`/`DoublyClosed`), and the frontier closure pair
(`frontier_doublyClosed`: `Z=96`, `N=152`; `frontier_occupancy = 248`) are named — so "why these
counts / where does it saturate" is a cost-functional question, not arithmetic.

## 2. Emission overlap: α and fission hindrance — C

An α decay (`nucleus → α + daughter`) and fission (`nucleus → fragments`) are composite →
fragment-cohort transitions. The amplitude is a **fragment overlap**, the analogue of
`PMHadrons.BoundStateOverlap`/`Emission` (`Γ = boundary × overlap² × phase space`). Here the
hindrance is *supplied*: `AlphaHindrance.alphaHindranceScale`, `AlphaConfiguration` mixing
(`alphaMixingV = κμδ = 1/200`, `hindrance = σχ/(χ·gap+1)`), `CollectiveE8.fissionBarrier =
shellWeight`, `FissionFissility`/`FissionFinite` fissility costs.

**Task.** Build the fragment overlap so the hindrance is computed, not supplied: the α/fission
fragment cohorts, the barrier as the boundary factor (`CollectiveE8.alphaBarrier_eq = 43`,
`fissionBarrier_eq = 43/6`), and the overlap from the fragment configurations — the direct transfer
of the hadron `Emission` construction. This reaches the collective/fission regime beyond the
`Z=96`, `N=152` frontier.

**Built (`FragmentOverlap`).** The interface exists: `fragmentOverlap` (fragment vs parent
configuration), `fragmentWidth = barrierRate · |overlap|² · phase` and `fragmentWidth_eq_partialWidth`
(`= |T|²·Φ` with `T = √barrierRate · overlap`). The barrier plays the Toll-boundary role; only the
fragment configuration (the overlap value) remains.

## 3. Governor: the nuclear rate / attempt-frequency layer — H/M

The rate *structure* is complete: `RateModel.betaSpectralRate*` (bounded by `β·c0`, monotone in the
cutoff, saturating), `CollectiveRate.barrierRate`/`MeanLife`, `PersistenceRate`, `AlphaFinite`;
`MeanLife`/`PersistenceRate` give rate → lifetime. The one input named is the **absolute attempt
frequency** `β·c0` and the E8 per-channel clock.

**Task.** Pin `β·c0` with the **Governor** per-slot credit (`χ/Δ = 2/43`,
`PMHadrons.TollGovernor.governorPerSlot`) — the same per-slot share that fixes the hadron cycle
persistence. This is the nuclear analogue of the hadron Governor work and closes the rate unit.

**Built (`NuclearRateUnit`).** The candidate identification is recorded: the per-slot attempt
frequency is the Governor credit `χ/Δ = 2/43` (`attemptFrequency`, `attemptFrequency_eq`), and a
channel's rate is `χ/Δ · Σ prob`, an instance of `RateModel.channelRate` with `β·c0 = χ/Δ`
(`governorChannelRate_eq`). The identification is the named model foundation to test.

## 4. Persistence selection: regime and valley — H

`NuclearRegime`/`NuclearDecay` split the smooth ledger (through the `Z=96`, `N=152` frontier) from
the collective ledger beyond it (`nuclearLedgerKind`, `regimePersists`); `NuclearSelection` /
`TransitionSelection` / `PersistenceRate` give least-cost / least-hazard selection;
`NuclearMass.PersistsMass` is mass-persistence.

**Open.** Which `(Z,N)` are stable (the valley) and the exact regime boundary — a persistence
selection using the barrier/rate layer, not mass minimality alone
(`CollectiveRate.not_collectivePersists_of_lower` shows mass minimality is the wrong criterion for
the post-frontier regime).

**Built (`PersistenceSelection`).** The exit table is wired into the rate layer:
`nuclearExitRateSystem` (its hazard is `collectiveRate (nuclearExitChannels …)`), and
`nuclearPersistsOn_iff` (`PersistsOn T ↔ T ≤ meanLife`, the exit table being nonempty). The
persistence-selected nuclide is the least-hazard one (`selectedNuclide_min`, from
`PersistenceRate`).

## Not the pattern (analysis / lattice / model input)

- **Charge tail** (§2) — the exact `3×3×3` lattice Coulomb Green function (`LatticeCharge3`,
  `LatticeCharge3Energy`: `q²·743/51`) does not scale to heavy nuclei by a global factor; needs a
  low-Z-anchored finite-size differential. Lattice analysis, not selection.
- **Spectral asymptotic** (§4) — `uniformResponse ~ n⁵/(16π)`; a limit theorem.
- **Neutrino decay / ordering** (§4b) — needs a decay channel and mass ordering (model).
- **Chemistry / Aufbau** (§6) — screening/exchange and the fill order are model inputs.
- **Certified-mass enclosure** (§7) — a rational enclosure of the `π`/`√` `certifiedMass`;
  interval analysis. **Built (`CertifiedNumerics`, `CertifiedEnclosure`)**: the `certifiedMass_eq`
  expansion, an `O(log n)` integer cube root (`cbrt`), computable `ℚ` bounds (`rpow23Lo`/
  `sqrtLo`…), and the **general** enclosure `certifiedMass_bounds` — `cmLo Z N d ≤
  certifiedMass Z N ≤ cmHi Z N d` for *any* nuclide at `d` digits (not an enumeration);
  `certifiedMass_c12` is the regression instance. Remaining: wire e8p's `--certified` readout.
- **Continuum-comparison modules** (§5b) — keep as numerical cross-checks until each E8
  replacement has a numeric counterpart.

## Consolidation (checkpoint)

Mark the candidate modules experimental; align `README`/`OVERVIEW`/`ATOM-SYSTEM`; keep residuals in
`RESIDUALS.md` outside the theorem tree; pass `./build.sh fast PMAtoms`, `./build.sh audit`,
`./build.sh e8p`.
