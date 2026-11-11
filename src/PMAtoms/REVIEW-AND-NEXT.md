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

## 1. Isospin and the bulk — H

`certifiedMass` is a stable-line ledger: it matches measured masses to `4.8 m_e` rms on the stable
line and has no valley above `A ≈ 56` (`IsospinLedger`, `RESIDUALS.md`). The E8 occupancy term
(separate `p`/`n` filling, `occupancySymmetry ≈ 8.3 MeV·(N−Z)²/A`) is the kinetic half of a
symmetry energy and puts Pb and U on the stable isobar (`valleyMass`); a consistent occupancy
ledger stops for lack of an E8 link potential (`IsospinLedger` docstring).

**Potential half (persistence filter).** Two identical nucleons in one link persist only in the
spin singlet (`1` of `spinStates² = 4` states); an unlike pair persists in all `4`. Weighting
links by persisting states, normalized to mean `w` at `N = Z`, gives a quadratic isospin term
(`IsospinLedger.persistBinding_eq`), `≈ 6 MeV·(N−Z)²/A`; with the occupancy term the total is
`≈ 14–15` MeV (standard `23.7`). With both in place of the alpha-cluster suppression the lowest
isobar is within two units of the stable one through Pb (`Z = 84` at `A = 208`) and nine at
U-238 (`101` vs `92`).

**Open.** The bulk: with both isospin terms present the stable-line masses are `≈ 110 m_e`
heavy on average, because `certifiedMass`'s bulk terms (and the alpha-cluster binding) already
carry the average symmetry cost along the line. A full-chart ledger needs the bulk re-derived
with the isospin terms present; the occupancy ledger's symmetric filling energy has no E8 link
potential to pair with (`IsospinLedger` docstring). Until then the valley (which `(Z, N)` are
stable, `NuclearRegime`/`PersistenceSelection`) is a comparison, not a result.

## Retained inputs and not pursued

- **Fragment overlap (α / fission hindrance).** The amplitude is a fragment overlap
  (`FragmentOverlap.fragmentWidth = barrierRate · |overlap|² · phase`, barriers E8:
  `alphaBarrier_eq = 43`, `fissionBarrier_eq = 43/6`). The overlap value is the same retained input
  as the hadron level's composite configuration (`PMHadrons.Emission`, `EmissionScale`), and is
  handled there. The E8 level schemes give the level costs; the odd-A α comparison is in
  `ALPHA-TESTS.md`.
- **Deformed frontier (Q3).** `Cm-244` is under-bound by `+44 m_e` at `Z = 96, N = 152`; it and
  `Cf-252` are boundary data past the certified domain (`RESIDUALS.md`). The `2(Δ+σ)=96` term
  overcorrects U-238 and the `−43/288` deformation candidate fails its holdout. Not pursued.
- **Volume/surface split (Q1).** Closed as a floor (`~3.3 m_e`); the persistence-selected packing
  count does not lower it (`RESIDUALS.md`).

## Not the pattern (analysis / lattice / model input)

- **Charge tail** (§2) — the exact `3×3×3` lattice Coulomb Green function (`LatticeCharge3`,
  `LatticeCharge3Energy`: `q²·743/51`) does not scale to heavy nuclei by a global factor; needs a
  low-Z-anchored finite-size differential. Lattice analysis, not selection.
- **Spectral asymptotic** (§4) — `uniformResponse ~ n⁵/(16π)`; a limit theorem.
- **Neutrino decay / ordering** (§4b) — needs a decay channel and mass ordering (model).
- **Chemistry / Aufbau** (§6) — screening and the fill order are model inputs. The spin rule is
  derived (`HundRule`: same-spin pairs maximized, Hund's first rule; ground multiplicities match
  `Z = 1–54` except the four Aufbau-order exceptions Cr, Nb, Mo, Pd, which match on their
  observed configurations).
- **Continuum-comparison modules** (§5b) — keep as numerical cross-checks until each E8
  replacement has a numeric counterpart.

## Consolidation (checkpoint)

Mark the candidate modules experimental; align `README`/`OVERVIEW`/`ATOM-SYSTEM`; keep residuals in
`RESIDUALS.md` outside the theorem tree; pass `./build.sh fast PMAtoms`, `./build.sh audit`,
`./build.sh e8p`.
