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
| **Governor** — per-slot persistence | `χ/Δ` per slot (`TollGovernor`) | the shell spacing `ℏω(A)`; the attempt-frequency candidate (`NuclearRateUnit`, compared in `ALPHA-TESTS.md`) |
| **persistence selection** | `SelectionSymmetry` | **regime / valley** selection |

## 1. Occupancy: the nucleus ledger — H/M

The nucleus mass is the free-nucleon sum minus the link/closure layers (`TwoLedger`,
`NuclearLedger.certifiedMass`). Along the stable line it matches measured masses to `4.8 m_e` rms
(`RESIDUALS.md`, which also holds the SEMF regression, the holographic check and the shell-term
comparison).

1. **Isospin restoring term and the bulk.** `certifiedMass` has no `(N−Z)²/A` term
   (`IsospinLedger`: links linear in `N−Z`, `typed_pn_mean`), so it has no valley above
   `A ≈ 56`. E8 gives a clear reason for one: protons and neutrons fill separate shell ladders
   (Capacity, spin `2`, spacing `ℏω(A)`), costing `occupancySymmetry ≈ 8.3 MeV·(N−Z)²/A`. It
   replaces the alpha-cluster isospin suppression, which is a second `N ≈ Z` preference for the
   same nucleons (`valleyMass`). With it the lowest isobar is `Z = 18, 24, 37, 47, 82, 92` at
   `A = 40, 56, 90, 120, 208, 238` (stable `20, 26, 40, 50, 82, 92`). The stable-line masses
   then come out `≈ 100 m_e` heavy on average (rms `53`): the bulk terms already carry the
   average symmetry cost. Most of that offset is the alpha-cluster binding
   itself (`Δ/D` per cluster, `43 m_e` at O-16 where the occupancy term is zero): the
   suppression `(1 − |N−Z|/Δ)` both sets the stable-line masses and is the ledger's isospin
   mechanism, so it cannot simply be swapped out. **Where it stops (no clear E8 rule).** A
   consistent occupancy ledger also needs the symmetric part of the filling energy,
   `(ℏω/2)(3/2)^{4/3}A^{1/3}` per nucleon `≈ 37.5` MeV with the E8 `ℏω(A)` (Fermi-gas mean kinetic
   energy `≈ 22` MeV). The link weights would then be a potential, not the net binding they are
   now (`πD`-based, matching the SEMF volume term), and nothing in the substrate gives a link
   potential separate from the net cost. So the rebuild has no E8 rule past the asymmetric term;
   `certifiedMass` stays the stable-line ledger and `valleyMass` the valley comparison. The potential part of the
   symmetry energy has no E8 reason yet (`pn` weight = mean of `pp`, `nn`); the light valley
   (`A = 40, 56` two units neutron-rich) is where it would show.
2. **(Deferred) Deformed closure / frontier (Q3).** `Cm-244` is under-bound by `+44 m_e` at the
   deformed closure `Z = 96, N = 152`. Held (boundary data past the certified domain). Subsumes: the `2(Δ+σ)=96` term
   overcorrects U-238, and the `−43/288` deformation candidate fails its holdout.

## 2. Emission overlap: α and fission hindrance — C

An α decay and fission are composite → fragment-cohort transitions with amplitude a **fragment
overlap**, the analogue of `PMHadrons.Emission` (`FragmentOverlap.fragmentWidth = barrierRate ·
|overlap|² · phase`). The barriers are E8 (`CollectiveE8.alphaBarrier_eq = 43`,
`fissionBarrier_eq = 43/6`).

**Open.** The overlap value, i.e. the fragment configuration. The E8 level schemes compared so
far (`ALPHA-TESTS.md`, `ShellGaps` §4) give the level *costs*; the observed odd-A hindrances
(U-235 `≈ +6.3`, Pu-239 `≈ +1.8`) match only the nonstandard `SingleParticle.nilssonEnergy`
formula. Both parents are deformed in the standard model; the E8 spectrum is spherical.

## 3. Persistence selection: regime and valley — H

The selection layer is built (`NuclearRegime`, `NuclearDecay`, `PersistenceSelection`,
`PersistenceRate`; see `OVERVIEW.md`). **Open:** the valley itself depends on §1 item 1: with the
current ledger, mass persistence selects the stable isobar only up to `A ≈ 40`. Past the
`Z = 96, N = 152` frontier, mass minimality is the wrong criterion
(`CollectiveRate.not_collectivePersists_of_lower`), and the barrier/rate layer selects.

## Not the pattern (analysis / lattice / model input)

- **Charge tail** (§2) — the exact `3×3×3` lattice Coulomb Green function (`LatticeCharge3`,
  `LatticeCharge3Energy`: `q²·743/51`) does not scale to heavy nuclei by a global factor; needs a
  low-Z-anchored finite-size differential. Lattice analysis, not selection.
- **Spectral asymptotic** (§4) — `uniformResponse ~ n⁵/(16π)`; a limit theorem.
- **Neutrino decay / ordering** (§4b) — needs a decay channel and mass ordering (model).
- **Chemistry / Aufbau** (§6) — screening/exchange and the fill order are model inputs.
- **Continuum-comparison modules** (§5b) — keep as numerical cross-checks until each E8
  replacement has a numeric counterpart.

## Consolidation (checkpoint)

Mark the candidate modules experimental; align `README`/`OVERVIEW`/`ATOM-SYSTEM`; keep residuals in
`RESIDUALS.md` outside the theorem tree; pass `./build.sh fast PMAtoms`, `./build.sh audit`,
`./build.sh e8p`.
