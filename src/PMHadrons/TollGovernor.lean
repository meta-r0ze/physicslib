import PMSubstrate.PersistenceEvents
import PMSubstrate.PhysicalBridge
import PMSubstrate.ImpedanceTerms
import PMSubstrate.PersistencePremises
import PMHadrons.Occupancy
import Mathlib.Tactic

/-!

# Toll and Governor at the composite level

Four of the six pillars set a composite's *room* (Map, Protocol, Margin as counts; Capacity in
every cell). The other two act on its **transitions**, and this module gives them their
composite-level role:

* **Toll** spends (Causality). A composite can shed a carrier only through a **boundary
  transition**: the exposed leg takes one of `χ = 2` orientations (`PMSubstrate.Orientation`), the
  target address must avoid the composite's own `σ` embedded addresses
  (`(R_M − σ)/R_M = 167/172`), and the channels and interaction direction are filtered. The
  composite's **emission boundary** is exactly the Toll event `PMSubstrate.ValidToll`, with weight
  `tollTerm` (`PMSubstrate.uniform_toll`). This is the boundary factor of a decay — the object the
  SM comparison calls `fπ`/`fK` (`REVIEW-AND-NEXT.md` item 2).

* **Governor** restricts (Causality). A credit over the `Δ`-cycle that the clock advance cannot
  distinguish is uniform, `χ/Δ = 2/43` per slot (`PMSubstrate.ImpedanceTerms.governor_uniform`), and
  over the cycle it totals `χ` (`governorCycleTotal`). This is the composite's **per-slot
  persistence** — how the clock keeps it going — the factor behind the rate/lifetime layer.

Everything here is E8-native; measured decay constants and lifetimes are the comparison.
-/

namespace PMHadrons.TollGovernor

open Finset
open PMSubstrate.E8Values

/-! ## Toll: the composite's emission boundary -/

/-- The composite's emission boundary: `χ = 2` orientations of the exposed leg times
`R_M − σ = 167` target addresses that avoid its own `σ` embedded addresses. It is the Toll event. -/
abbrev EmissionBoundary := PMSubstrate.ValidToll

theorem emissionBoundary_card : Fintype.card EmissionBoundary = 334 := by
  simp [EmissionBoundary, PMSubstrate.ValidToll]

/-- **The emission boundary weight is the Toll term** (`PMSubstrate.uniform_toll`). -/
theorem emissionBoundary_weight :
    (PMSubstrate.tollEvent.card : ℝ) / Fintype.card PMSubstrate.TollSpace =
      PMSubstrate.tollTerm PMSubstrate.baseline :=
  PMSubstrate.uniform_toll

/-- A carrier cannot be emitted into the composite's own `σ` embedded addresses: the
non-aliasing target fraction is `(R_M − σ)/R_M = 167/172` (`PMSubstrate.TollFilters.nonaliasing_prob`). -/
theorem emission_nonaliasing :
    (((RM : ℝ) - (sigma : ℝ)) / (RM : ℝ)) = 167 / 172 := by
  rw [PMSubstrate.E8Values.RM_eq, PMSubstrate.E8Values.sigma_eq]
  norm_num

/-- The self-aliasing fraction a boundary transition must avoid, `σ/R_M = 5/172`. -/
theorem emission_self_aliasing : ((sigma : ℝ) / (RM : ℝ)) = 5 / 172 := by
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.RM_eq]
  norm_num

/-! ## Governor: the composite's cycle persistence -/

/-- **The composite's per-slot persistence credit.** A `χ`-credit over the `Δ`-cycle invariant
under the clock advance is uniform, `χ/Δ = 2/43` per slot
(`PMSubstrate.ImpedanceTerms.governor_uniform`). -/
theorem governorPerSlot (f : ZMod 43 → ℝ) (h : ∀ i, f (i + 1) = f i)
    (htot : ∑ i, f i = 2) : ∀ i, f i = 2 / 43 :=
  PMSubstrate.ImpedanceTerms.governor_baseline f h htot

/-- **The composite's cycle persistence totals `χ` over the `Δ` slots.** -/
theorem governorCycleTotal : (43 : ℝ) * (2 / 43) = 2 := by norm_num

/-- Governor restricts: it never increases the transition count
(`PMSubstrate.PersistencePremises.restriction_lowers`). -/
theorem governor_restricts {T : Type*} (B : Finset T) (keep : T → Prop) [DecidablePred keep] :
    (B.filter keep).card ≤ B.card :=
  PMSubstrate.PersistencePremises.restriction_lowers B keep

/-! ## Both pillars are already in the cell cost -/

/-- The composite's per-cell cost is the sum of all six pillars (`PMSubstrate.impedance`), so Toll
and Governor are paid in every cell; the roles above are their *transition* manifestations. -/
theorem cellBudget_eq_six :
    PMSubstrate.impedance PMSubstrate.baseline =
      PMSubstrate.capacityTerm PMSubstrate.baseline + PMSubstrate.mapTerm PMSubstrate.baseline +
        PMSubstrate.protocolTerm PMSubstrate.baseline +
          PMSubstrate.governorTerm PMSubstrate.baseline +
            PMSubstrate.tollTerm PMSubstrate.baseline +
              PMSubstrate.marginTerm PMSubstrate.baseline :=
  rfl

end PMHadrons.TollGovernor
