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
    push_neg at hc
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

end PersistenceMechanics.ImpedanceMatching
