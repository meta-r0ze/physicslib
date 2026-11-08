# PMChemistry — open work (todo)

Checked mathematics is in [OVERVIEW.md](OVERVIEW.md). This file is only open work.
Run `./build.sh PMChemistry` for current counts.

## 1. Justify the Aufbau order
The Madelung order `(n+ℓ, n)` is supplied (`Aufbau.aufbau`, stated and sorted in
`aufbau_sorted`). Derive it — or a screening correction to the hydrogenic energy —
so the fill order is a consequence of persistence/E8 rather than a rule of thumb.
The capacities are already E8 (`PMAtoms.Shells`); the order is the missing piece.

## 2. Screening and exchange
`PMAtoms.ElectronCloud.orbitalEnergyEV = −R∞/n²` ignores electron–electron
screening and exchange. Add those terms (or their E8 counterpart) so shell energies
and ionization order match, which would also settle §1.

## 3. Valence and bonding
The `60°`/tetrahedral shell interaction named in `PMAtoms/REVIEW-AND-NEXT.md` §6
belongs here: valence geometry, bond formation, and why configurations with full
shells persist (noble gases).

## 4. Periodic-table structure
Groups, periods and valence recurrence are not formalised. The `e8p`
periodic-table readout (`tools/e8p/E8PConstants/Periodic.lean`) currently owns both
the display order and the configuration; it could import `PMChemistry.Aufbau`
instead of duplicating the order.

## Verification

Run `./build.sh PMChemistry`. No later-paper imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
