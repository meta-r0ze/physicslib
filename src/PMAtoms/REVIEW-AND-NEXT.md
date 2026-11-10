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

**Open.**

1. **Deformed proton closure `2(Δ+σ)=96`** (§3). Recorded, but a simple closure term overcorrects
   U-238; refine it (apply only past the frontier, or soften it).
2. **N=Z saturation** (§1b). Every N=Z nucleus past O-16 is over-bound by ≈`1.1–1.2 m_e` per alpha
   cluster (`RESIDUALS.md`: Ne-20 −7.6, Ca-40 −12.3, Ni-56 −16.4 `m_e`); the alpha closure lacks a
   saturation once a closed core exists. The complex's surface law is ruled out (wrong direction).
   Derive the saturation from the occupancy.
3. **Heavy deformation shape** (§1). The collective occupancy of a heavy nucleus; the candidate
   `− (43/288)·max((Z−82)(N−126) − 82, 0)` holds the training set to `±0.008 u` but the holdout
   (Pu/Cm/Cf/Fm/No/Rf) scatters `−0.019…+0.018 u`. Needs a mid-shell/Z-dependent occupancy factor or
   shape coexistence; do **not** integrate until the holdout passes.

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
