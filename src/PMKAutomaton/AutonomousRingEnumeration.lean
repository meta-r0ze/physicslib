import PMKAutomaton.AutonomousRing

/-! Exhaustive kernel certificate for the requested eight-state rule space. -/
namespace PMKAutomaton.AutonomousRing

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem admissible_rules_count : admissibleRules.card = 10 := by decide +kernel

theorem explicit_rules_exhaustive : explicitRules = admissibleRules := by
  apply Finset.eq_of_subset_of_card_le
  · intro f hf
    obtain ⟨⟨k,b⟩,_,rfl⟩ := Finset.mem_image.mp hf
    exact (enumeration_complete _).mpr (explicit_admissible k b)
  · rw [admissible_rules_count,explicit_rules_card]


end PMKAutomaton.AutonomousRing
