import PMConstants.ReferenceMaintenance
import PMConstants.TableConsequences

/-!
# Executable conditional ledgers and a partition countermodel

The retained-record protocol realizes the supplied resource tasks. Its events
are coordinate swaps in a finite task model, not certified substrate primitives.
The ledger weights remain supplied prices, including the fractional payload price.

An alternative partition moves the spatial resource to weak. It restores exactly
the same total resource set with the same minimal combined price. Thus reversible
restoration, coverage and additive Economy alone do not force weak confinement
to the clock. A sector-specific capability/requirement law is still needed.
-/

noncomputable section
namespace PMConstants.ReferenceMaintenanceLedger
open PMConstants GaugeLedgers ReferenceMaintenance

theorem weight_positive (r : Res) : 0 < weight r := by
  cases r <;> norm_num [weight, overhead]

theorem executable_ledger (req : Finset Res) :
    Restores req req.toList ∧
      MinimalRefresh.cost weight req.toList = ledger req ∧
      IsLeast {c | ∃ L, Restores req L ∧ MinimalRefresh.cost weight L = c} (ledger req) :=
  ⟨canonical_restores req, (MinimalRefresh.minimal_attained weight req).2,
    minimum_executable_cost weight (fun r => (weight_positive r).le) req⟩

/-- For the specified requirement table, the three minimum executable prices. -/
theorem standard_prices :
    MinimalRefresh.cost weight reqSU2.toList = 43 ∧
      MinimalRefresh.cost weight reqY.toList = 129 + 5 + 16 * overhead ∧
      MinimalRefresh.cost weight reqColour.toList = ColourChannels.colourLedger := by
  rw [(executable_ledger reqSU2).2.1, (executable_ledger reqY).2.1,
    (executable_ledger reqColour).2.1, su2_value, hyper_value, colour_value]
  exact ⟨rfl, rfl, rfl⟩

/-- Connect an actual supplied assignment to executable schedules, rather than
using the numerical ledger consequences as proof of that assignment. -/
theorem assignment_executable (P : TableConsequences.Premises) :
    (∀ r, (P.f r = .weak ↔ r ∈ reqSU2) ∧ (P.f r = .hyper ↔ r ∈ reqY)) ∧
      Restores reqSU2 reqSU2.toList ∧ Restores reqY reqY.toList :=
  ⟨TableConsequences.assignment P, canonical_restores reqSU2, canonical_restores reqY⟩

def alternativeWeak : Finset Res := insert .space reqSU2
def alternativeHyper : Finset Res := reqY.erase .space

theorem alternative_partition :
    Disjoint alternativeWeak alternativeHyper ∧
      alternativeWeak ∪ alternativeHyper = reqSU2 ∪ reqY := by
  constructor
  · rw [Finset.disjoint_left]
    intro r hw hy
    simp only [alternativeWeak, reqSU2, Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [alternativeHyper, Finset.mem_erase] at hy
    rcases hw with h | h
    · exact hy.1 h
    · subst r
      simpa [reqY] using hy.2
  · ext r
    simp only [alternativeWeak, alternativeHyper, Finset.mem_union,
      Finset.mem_insert, Finset.mem_erase]
    have hs : Res.space ∈ reqY := by simp [reqY]
    by_cases h : r = .space
    · subst r; simp [hs]
    · simp [h]

theorem alternative_weak_price : ledger alternativeWeak = 172 := by
  norm_num [alternativeWeak, ledger, reqSU2, weight]

theorem alternative_hyper_price : ledger alternativeHyper = 5 + 16 * overhead := by
  have hs : Res.space ∈ reqY := by simp [reqY]
  have h := Finset.sum_erase_add reqY weight hs
  change ledger alternativeHyper + weight .space = ledger reqY at h
  rw [hyper_value] at h
  norm_num [weight] at h
  linarith

/-- The alternative is executable, with each required job occurring once; its
combined minimum work is unchanged. This is not an alternative physical theory. -/
theorem alternative_same_total :
    Restores alternativeWeak alternativeWeak.toList ∧
      Restores alternativeHyper alternativeHyper.toList ∧
      ledger alternativeWeak + ledger alternativeHyper = footprint ∧
      ledger alternativeWeak ≠ ledger reqSU2 := by
  refine ⟨canonical_restores _, canonical_restores _, ?_, ?_⟩
  · rw [alternative_weak_price, alternative_hyper_price]
    unfold footprint
    ring
  · rw [alternative_weak_price, su2_value]
    norm_num

end PMConstants.ReferenceMaintenanceLedger
