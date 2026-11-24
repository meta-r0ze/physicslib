import PMAction.ReferenceNodeBoundary

/-!
# Alternating visits to a retained reference node

Each cycle supplies fresh incoherent populations from the right and then the
left. Each visit exports the external output and keeps the updated center
for the next visit. The current is per cycle. The duration and realization
of the two visits by a native trace are separate inputs.
-/

noncomputable section
namespace PMAction.AlternatingReferenceNode

/-- A visit adds the injected population to the retained center. -/
def visit (w retained incoming : ℝ) : ℝ := retained + w * (incoming - retained)

/-- The center is the retained output of both successive visits. -/
def step (w l r x : ℝ) : ℝ := visit w (visit w x r) l

/-- The cycle-fixed population immediately before the visit from the right. -/
def fixedCenter (w l r : ℝ) : ℝ := (l + (1 - w) * r) / (2 - w)

/-- The center deviation is multiplied by the stay weight at each visit. -/
theorem step_sub_fixed (w l r x : ℝ) (hw : w ≤ 1) :
    step w l r x - fixedCenter w l r = (1 - w) ^ 2 * (x - fixedCenter w l r) := by
  have h : 2 - w ≠ 0 := by linarith
  unfold step fixedCenter visit
  field_simp
  ring

theorem fixed_iff (w l r x : ℝ) (hpos : 0 < w) (hw : w ≤ 1) :
    step w l r x = x ↔ x = fixedCenter w l r := by
  have hstep := step_sub_fixed w l r x hw
  constructor
  · intro h
    rw [h] at hstep
    have hz : (w * (2 - w)) * (x - fixedCenter w l r) = 0 := by
      linear_combination hstep
    have hp : 0 < w * (2 - w) := mul_pos hpos (by linarith)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hp.ne')
  · intro h
    subst x
    rw [sub_self, mul_zero] at hstep
    exact sub_eq_zero.mp hstep

/-- The right visit injects exactly the amount that the left visit exports
in the fixed cycle. -/
theorem fixed_current (w l r : ℝ) (hpos : 0 < w) (hw : w ≤ 1) :
    let x := fixedCenter w l r
    let y := visit w x r
    y - x = w / (2 - w) * (r - l) ∧
      y - visit w y l = w / (2 - w) * (r - l) := by
  intro x y
  have h : 2 - w ≠ 0 := by linarith
  have hright : y - x = w / (2 - w) * (r - l) := by
    dsimp [y, x, fixedCenter, visit]
    field_simp
    ring
  have hx : visit w y l = x := (fixed_iff w l r x hpos hw).mpr rfl
  exact ⟨hright, by rwa [hx]⟩

/-- Even with equal local weights the alternated current differs from the
simultaneous series conductance, since the center changes between visits. -/
theorem series_lt_cycle (w : ℝ) (hpos : 0 < w) (hw : w ≤ 1) :
    ReferenceNodeBoundary.series w w < w / (2 - w) := by
  rw [ReferenceNodeBoundary.equal_floating w hpos, lt_div_iff₀ (by linarith)]
  nlinarith [sq_pos_of_pos hpos]

end PMAction.AlternatingReferenceNode
