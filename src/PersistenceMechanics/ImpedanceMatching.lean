import Mathlib.Tactic

/-!
# Nested Rule 3: Impedance Matching

The interface rule of Nested Persistence (`PM-3-Nested/paper/2_nested_persistence.tex`,
"Impedance Matching"), for the positive-real interface law used there. Source and load
impedances `Z_s, Z_l` give the reflection coefficient `r = (Z_l − Z_s)/(Z_l + Z_s)` and the
transmission `T = 1 − r²`.

* `ledger`: an incident load `P` splits as `P r² + P T = P`. Reflection stays in this
  conserved ledger; it is not erasure.
* `reflection_sq_lt_one`: for positive impedances `r² < 1`.
* `admissible_iff_transmission`: reflected load within a reserve `B`, `P r² ≤ B`, is
  equivalent to `T ≥ 1 − B/P`.
* `zero_reserve_matched`: with zero reserve, exact matching `Z_l = Z_s` is necessary.
* `realize`: every coefficient `s` is attained by source `1 − s` and load `1 + s`
  (positive when `|s| < 1`).

The rule is a budget condition, not an optimality claim: with positive reserve a
mismatched interface can be admissible. No substrate is assumed here.
-/

namespace PersistenceMechanics.ImpedanceMatching

/-- Reflection coefficient of a positive-real interface. -/
noncomputable def reflection (Zs Zl : ℝ) : ℝ := (Zl - Zs) / (Zl + Zs)

/-- Transmitted fraction `T = 1 − r²`. -/
noncomputable def transmission (Zs Zl : ℝ) : ℝ := 1 - reflection Zs Zl ^ 2

/-- **The conserved ledger.** Reflected plus transmitted load is the incident load. -/
theorem ledger (Zs Zl P : ℝ) :
    P * reflection Zs Zl ^ 2 + P * transmission Zs Zl = P := by
  unfold transmission
  ring

/-- For positive impedances the reflected fraction is below one. -/
theorem reflection_sq_lt_one {Zs Zl : ℝ} (hs : 0 < Zs) (hl : 0 < Zl) :
    reflection Zs Zl ^ 2 < 1 := by
  unfold reflection
  have h : 0 < Zl + Zs := by linarith
  rw [div_pow, div_lt_one (by positivity)]
  nlinarith [mul_pos hs hl]

/-- **Admissibility.** Reflected load within the reserve is a transmission floor. -/
theorem admissible_iff_transmission {P B : ℝ} (hP : 0 < P) (Zs Zl : ℝ) :
    P * reflection Zs Zl ^ 2 ≤ B ↔ 1 - B / P ≤ transmission Zs Zl := by
  unfold transmission
  rw [sub_le_sub_iff_left, le_div_iff₀ hP, mul_comm]

/-- **Zero reserve forces exact matching.** -/
theorem zero_reserve_matched {P : ℝ} (hP : 0 < P) {Zs Zl : ℝ} (hs : 0 < Zs) (hl : 0 < Zl)
    (h : P * reflection Zs Zl ^ 2 ≤ 0) : Zl = Zs := by
  have hr : reflection Zs Zl ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hP hc
    linarith
  have h2 : reflection Zs Zl ^ 2 = 0 := le_antisymm hr (sq_nonneg _)
  have h0 : reflection Zs Zl = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  unfold reflection at h0
  have hsum : Zl + Zs ≠ 0 := by linarith
  rcases div_eq_zero_iff.mp h0 with h0 | h0
  · linarith
  · exact absurd h0 hsum

/-- **Every coefficient is realized.** Source `1 − s`, load `1 + s`. -/
theorem realize (s : ℝ) : reflection (1 - s) (1 + s) = s := by
  unfold reflection
  ring

theorem reflection_zero_iff {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    reflection source load = 0 ↔ load = source := by
  simp [reflection, div_eq_zero_iff, ne_of_gt (add_pos hl hs), sub_eq_zero]

theorem transmission_formula {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    transmission source load = 4*source*load/(load+source)^2 := by
  have hn : load+source ≠ 0 := ne_of_gt (add_pos hl hs)
  unfold transmission reflection
  field_simp [hn]
  ring

theorem transmission_bounds {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    0 < transmission source load ∧ transmission source load ≤ 1 := by
  constructor
  · rw [transmission_formula hs hl]
    positivity
  · unfold transmission
    nlinarith [sq_nonneg (reflection source load)]

theorem perfect_matching_iff {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    transmission source load = 1 ↔ load = source := by
  have h : transmission source load = 1 ↔ (reflection source load)^2 = 0 := by
    unfold transmission
    constructor <;> intro hx <;> linarith
  rw [h, sq_eq_zero_iff, reflection_zero_iff hs hl]

noncomputable def reflected (incident source load : ℝ) : ℝ := incident * (reflection source load)^2
noncomputable def transmitted (incident source load : ℝ) : ℝ := incident * transmission source load
def Admissible (incident reserve source load : ℝ) : Prop := reflected incident source load ≤ reserve


theorem reflected_nonneg {incident source load : ℝ} (hp : 0 ≤ incident) :
    0 ≤ reflected incident source load := mul_nonneg hp (sq_nonneg _)

theorem zero_reflection_iff {incident source load : ℝ}
    (hp : 0 < incident) (hs : 0 < source) (hl : 0 < load) :
    reflected incident source load = 0 ↔ load = source := by
  rw [reflected, mul_eq_zero, or_iff_right hp.ne', sq_eq_zero_iff,
    reflection_zero_iff hs hl]

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

end PersistenceMechanics.ImpedanceMatching
