# PMSubstrate — open work (todo)

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

Checked mathematics is in [`OVERVIEW.md`](OVERVIEW.md). This file lists what is still
missing. The main theorem is conditional on the postulates in `OVERVIEW.md`; the open
items are the arrows from persistence to those postulates and from the substrate to the
measured coupling.

## Missing implications

| Intended step | What is needed | Why the current premise is insufficient |
| --- | --- | --- |
| Persistent vacuum -> lattice | Derive an additive discrete address structure and integral quadratic cost from independently specified vacuum constraints | Finite resources or finite descriptions admit many graphs and state spaces; neither forces a lattice or a quadratic cost. |
| Conservation -> theta symmetries | Explain why the vacuum's state enumeration must have the specified T and S transformation laws | Preservation of identity, or even bijective evolution, does not imply modular transformations of a statistical state sum. |
| Persistence -> minimum rank | Establish the comparison family, cost functional, weights, selection dynamics and why higher ranks are excluded | Survival bias is conditional on hazard and prior assumptions; persistence does not assert global minimization. Even unimodular lattices also exist above rank eight. |
| E8 -> clock/sectors/costs | Derive the physical sector choice, clock interpretation, events, weights, signs, saturation and normalizations | Existence of these objects in E8 does not prove that the vacuum dynamics selects or uses them. |
| Geometric index -> electromagnetic response | Compute the normalized infrared electromagnetic response from that same dynamics | Defining a reciprocal index or assuming the Maxwell matching coefficient does not compute the physical coupling. |

## Occupancy cost

- Connect the counts of occupied clock regions to physical footprints. The physical event unit is in [SCOPE](../../SCOPE.md#named-premises).

## Current priority

Specify the microscopic vacuum state, update, probe and physical operator sectors without
mentioning E8, 43, the six-term expression or the target decimal. Then require each
selection theorem to rule out alternatives within that explicitly stated class.


The alternative routes and necessity tests are in `PMSubstrate/Research/`.

## Downstream constants to repoint

- Repoint α aliases to `causalCoupling` in `SharedUnits.αe`, `CarrierAmplitude.alpha` and `MuonLifetimeCorrected.α`.
- Repoint reciprocal aliases to `geometricIndex` in `SharedUnits.αinv`
  and `CKM.αinv`. Keep the separate cell-price reading and its equality.
- Repoint the PMAtoms.Invariants.Δ alias to E8Values.Delta.
  Use it for the receiver clock size when the type expresses the baseline ring.
