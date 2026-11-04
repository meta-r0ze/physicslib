import PMConstants.Interface

/-! A general positive-real interface with a reflected-load budget. Reflection
and transmission remain in the conserved ledger. Calling reflection irretrievable
dissipation, or identifying this law with a substrate interface, is extra physics.
-/
noncomputable section
namespace PMConstants.General.Matching
open PMConstants.Interface

def reflected (incident source load : ℝ) : ℝ := incident * (reflection source load)^2
def transmitted (incident source load : ℝ) : ℝ := incident * transmission source load
def Admissible (incident reserve source load : ℝ) : Prop := reflected incident source load ≤ reserve

theorem load_conserved (incident source load : ℝ) :
    reflected incident source load + transmitted incident source load = incident := by
  unfold reflected transmitted transmission
  ring

theorem reflected_nonneg {incident source load : ℝ} (hp : 0 ≤ incident) :
    0 ≤ reflected incident source load := mul_nonneg hp (sq_nonneg _)

theorem zero_reflection_iff {incident source load : ℝ}
    (hp : 0 < incident) (hs : 0 < source) (hl : 0 < load) :
    reflected incident source load = 0 ↔ load = source := by
  rw [reflected, mul_eq_zero, or_iff_right hp.ne', sq_eq_zero_iff,
    reflection_zero_iff hs hl]

/-- The tolerance follows from an explicitly supplied reserve budget. -/
theorem budget_iff_transmission {incident reserve source load : ℝ} (hp : 0 < incident) :
    Admissible incident reserve source load ↔
      1-reserve/incident ≤ transmission source load := by
  unfold Admissible reflected transmission
  constructor
  · intro h
    have hr : (reflection source load)^2 ≤ reserve/incident :=
      (le_div_iff₀ hp).mpr (by nlinarith)
    linarith
  · intro h
    have hr : (reflection source load)^2 ≤ reserve/incident := by linarith
    have hb := (le_div_iff₀ hp).mp hr
    nlinarith

/-- Zero reserve forces exact matching within this reflected-load model. -/
theorem zero_reserve_iff {incident source load : ℝ}
    (hp : 0 < incident) (hs : 0 < source) (hl : 0 < load) :
    Admissible incident 0 source load ↔ load = source := by
  unfold Admissible
  rw [show reflected incident source load ≤ 0 ↔ reflected incident source load = 0 from
    ⟨fun h => le_antisymm h (reflected_nonneg hp.le), fun h => h.le⟩]
  exact zero_reflection_iff hp hs hl

/-- A mismatch can have positive transmission and fit a positive reserve.
This example supplies no numerical tolerance for the vacuum. -/
theorem mismatch_within_budget :
    Admissible 1 (1/8) 1 2 ∧ (1 : ℝ) ≠ 2 ∧
      reflected 1 1 2 = 1/9 ∧ transmitted 1 1 2 = 8/9 := by
  norm_num [Admissible, reflected, transmitted, reflection, transmission]

end PMConstants.General.Matching
