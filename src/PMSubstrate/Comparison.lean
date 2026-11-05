import PMSubstrate.Impedance
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate

/-!
# Postulate R

* `never_merge_iff_bijective`: on a finite state space, an update never merges two distinct
  states at any time iff it is bijective (Postulate R as an exact translation).

The measured α comparisons live in `PMSubstrate.ExperimentalComparison`.
-/

namespace PMSubstrate

/-- **Postulate R as an exact translation.** On a finite state space, no two distinct states
are ever merged by the evolution iff the update is bijective. -/
theorem never_merge_iff_bijective {X : Type*} [Finite X] (U : X → X) :
    (∀ t : ℕ, Function.Injective (U^[t])) ↔ Function.Bijective U := by
  constructor
  · intro h
    exact Finite.injective_iff_bijective.mp (by simpa using h 1)
  · intro h t
    exact h.1.iterate t

end PMSubstrate
