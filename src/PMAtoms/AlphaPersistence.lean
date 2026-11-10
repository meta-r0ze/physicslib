import PMAtoms.TwoLedger
import Mathlib.Tactic

/-!
# Alpha persistence as a phase count

The surviving-budget rule is made explicit as a count of substrate clock phases.
A gap `g` blocks the first `g` phases of the `Δ`-period; the remaining
`Δ − g` phases survive.  The alpha occupancy is capacity times the surviving
phase fraction.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- Phases of the `Δ`-period that survive an isospin gap `gap`. -/
def survivingPhases (gap : Nat) : Finset (Fin Δ) :=
  if h : gap ≤ Δ then
    (Finset.univ : Finset (Fin (Δ - gap))).image
      (fun i => ⟨gap + i.val, by
        have := i.isLt
        omega⟩)
  else ∅

/-- The surviving phase count is `Δ − gap`. -/
theorem survivingPhases_card (gap : Nat) (h : gap ≤ Δ) :
    (survivingPhases gap).card = Δ - gap := by
  unfold survivingPhases
  rw [dite_eq_left h]
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simp at hval
    omega

/-- Once the gap reaches the period, no phase survives. -/
theorem survivingPhases_card_of_ge (gap : Nat) (h : Δ ≤ gap) :
    (survivingPhases gap).card = 0 := by
  by_cases hle : gap ≤ Δ
  · have hcard := survivingPhases_card gap hle
    rw [hcard]
    omega
  · unfold survivingPhases
    rw [dite_eq_right hle]
    simp

/-- Fraction of the `Δ`-period that survives. -/
def alphaPhaseFraction (gap : Nat) : ℝ :=
  (survivingPhases gap).card / (Δ : ℝ)

theorem alphaPhaseFraction_eq (gap : Nat) (h : gap ≤ Δ) :
    alphaPhaseFraction gap = ((Δ - gap : Nat) : ℝ) / (Δ : ℝ) := by
  unfold alphaPhaseFraction
  rw [survivingPhases_card gap h]

theorem alphaPhaseFraction_eq_zero_of_ge (gap : Nat) (h : Δ ≤ gap) :
    alphaPhaseFraction gap = 0 := by
  unfold alphaPhaseFraction
  rw [survivingPhases_card_of_ge gap h]
  simp

/-- Alpha occupancy from the surviving phase count. -/
def alphaCountPhase (z n : Nat) : ℝ :=
  if 4 ≤ z + n then
    alphaCapacity z n * alphaPhaseFraction (isospinGap z n)
  else 0

theorem alphaPhaseFraction_eq_budget (z n : Nat) :
    alphaPhaseFraction (isospinGap z n) =
      (isospinBudget z n : ℝ) / (Δ : ℝ) := by
  by_cases h : isospinGap z n < Δ
  · have hle : isospinGap z n ≤ Δ := le_of_lt h
    rw [alphaPhaseFraction_eq (isospinGap z n) hle]
    unfold isospinBudget
    rw [ite_eq_left h]
  · have hge : Δ ≤ isospinGap z n := le_of_not_gt h
    rw [alphaPhaseFraction_eq_zero_of_ge (isospinGap z n) hge]
    unfold isospinBudget
    rw [ite_eq_right h]
    simp

/-- Phase-count occupancy equals the budget occupancy. -/
theorem alphaCountPhase_eq_budget (z n : Nat) :
    alphaCountPhase z n = alphaCountBudget z n := by
  unfold alphaCountPhase alphaCountBudget
  by_cases hA : 4 ≤ z + n
  · rw [ite_eq_left hA, ite_eq_left hA]
    rw [alphaPhaseFraction_eq_budget]
    ring
  · rw [ite_eq_right hA, ite_eq_right hA]

/-- Phase-count occupancy equals the original alpha count. -/
theorem alphaCountPhase_eq (z n : Nat) :
    alphaCountPhase z n = alphaCount z n := by
  rw [alphaCountPhase_eq_budget, ← alphaCount_eq_budget]


/-- Phases blocked by an isospin gap `gap`. -/
def blockedPhases (gap : Nat) : Finset (Fin Δ) :=
  if h : gap ≤ Δ then
    (Finset.univ : Finset (Fin gap)).image
      (fun i => ⟨i.val, by
        have := i.isLt
        omega⟩)
  else ∅

theorem blockedPhases_card (gap : Nat) (h : gap ≤ Δ) :
    (blockedPhases gap).card = gap := by
  unfold blockedPhases
  rw [dite_eq_left h]
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin Δ => x.val) hij

/-- Blocked plus surviving phases fill the `Δ` period. -/
theorem blocked_surviving_card_sum (gap : Nat) (h : gap ≤ Δ) :
    (blockedPhases gap).card + (survivingPhases gap).card = Δ := by
  rw [blockedPhases_card gap h, survivingPhases_card gap h]
  omega

/-- The isospin budget plus the gap is one full period. -/
theorem isospinBudget_add_gap (z n : Nat) (h : isospinGap z n < Δ) :
    isospinBudget z n + isospinGap z n = Δ := by
  unfold isospinBudget
  rw [ite_eq_left h]
  omega

theorem alphaCount_nonneg (z n : Nat) : 0 ≤ alphaCount z n := by
  rw [alphaCount_eq_budget]
  exact alphaCountBudget_nonneg z n

theorem alphaCount_zero_of_gap_ge (z n : Nat) (h : Δ ≤ isospinGap z n) :
    alphaCount z n = 0 := by
  unfold alphaCount
  by_cases hA : 4 ≤ z + n
  · rw [ite_eq_left hA, ite_eq_right (not_lt.mpr h)]
  · rw [ite_eq_right hA]

theorem alphaCount_le_capacity (z n : Nat) (hA : 4 ≤ z + n) :
    alphaCount z n ≤ alphaCapacity z n := by
  rw [alphaCount_eq_budget]
  exact alphaCountBudget_le_capacity z n hA

end PMAtoms
