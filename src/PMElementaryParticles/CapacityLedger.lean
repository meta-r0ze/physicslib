import PersistenceMechanics.CapacityPartitioning

/-!
# Capacity Partitioning on the clock ring

Nested Rule 1 (`PersistenceMechanics.CapacityPartitioning`) on the K-Automaton. One receiver
ring offers `Δ = 43` exchange opportunities per clock period
(`PMKAutomaton.Components.ring_exchange_full_load`; the ring has `Δ` sites,
`PMKAutomaton.ClockRing`). Protocols sharing a ring are the tasks. Each protocol's demand is
its registrations per period, and its interface overhead is any extra paid comparison.

* `ring_budget`: the shared ring is feasible only if registrations plus overhead fit in
  the period.
* `ring_protocol_bound`: if every protocol meets the Toll floor (at least one registration
  per period), at most `Δ = 43` protocols share one ring.
* `ring_protocol_bound_reserve`: with a Margin reserve `R` kept free, at most `43 − R`.

These are budget bounds. They do not say which protocols share a ring.
-/

namespace PMElementaryParticles.CapacityLedger

open Finset

/-- **Ring budget.** -/
theorem ring_budget {k : ℕ} (r h : Fin k → ℝ) (hcap : ∑ i, r i + ∑ i, h i ≤ 43) :
    ∑ i, (r i + h i) ≤ 43 := by
  rw [Finset.sum_add_distrib]
  exact hcap

/-- **At most `Δ` protocols per ring.** Each meets the Toll floor; overheads are nonnegative. -/
theorem ring_protocol_bound {k : ℕ} (r h : Fin k → ℝ) (hr : ∀ i, 1 ≤ r i)
    (hh : ∀ i, 0 ≤ h i) (hcap : ∑ i, r i + ∑ i, h i ≤ 43) : k ≤ 43 := by
  have h1 : (k : ℝ) ≤ ∑ i, r i := by
    calc (k : ℝ) = ∑ _i : Fin k, (1 : ℝ) := by simp
      _ ≤ ∑ i, r i := Finset.sum_le_sum fun i _ => hr i
  have h2 : 0 ≤ ∑ i, h i := Finset.sum_nonneg fun i _ => hh i
  exact_mod_cast (show (k : ℝ) ≤ 43 by linarith)

/-- **With a Margin reserve.** Keeping `R` opportunities free leaves room for at most
`43 − R` protocols. -/
theorem ring_protocol_bound_reserve {k : ℕ} (R : ℝ) (r h : Fin k → ℝ) (hr : ∀ i, 1 ≤ r i)
    (hh : ∀ i, 0 ≤ h i) (hcap : ∑ i, r i + ∑ i, h i + R ≤ 43) : (k : ℝ) ≤ 43 - R := by
  have h1 : (k : ℝ) ≤ ∑ i, r i := by
    calc (k : ℝ) = ∑ _i : Fin k, (1 : ℝ) := by simp
      _ ≤ ∑ i, r i := Finset.sum_le_sum fun i _ => hr i
  have h2 : 0 ≤ ∑ i, h i := Finset.sum_nonneg fun i _ => hh i
  linarith

end PMElementaryParticles.CapacityLedger
