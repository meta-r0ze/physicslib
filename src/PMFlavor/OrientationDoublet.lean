import Mathlib.Tactic

/-!
# If the weak doublet is the wall orientation, every move flips it

Candidate (PMAction REVIEW, "Colour register", survivor (a)): a generation is a pair of distinct
nontrivial classes, one per wall, and its two orientations, which class sits on which wall, are the
weak partners. Label the three classes by `Fin 3` and call a pair `(t, f)` (wall `T`, wall `F`)
positively oriented when `f = t + 1`; `PMAction.GenerationWalls.side` fixes one such convention.

* `wall_F_shift_flips`, `wall_T_shift_flips`: a single-wall shift, which changes the class on one
  wall to the third class and so changes the generation (`PMAction.GenerationLabel.single_wall_shift`),
  always reverses the orientation.
* `root_move_flips`: the root move by the generation's label exchanges the two classes
  (`register_candidates_check.py`, T5), keeping the generation and reversing the orientation.
* `no_neutral_change`: so no single move changes the generation and keeps the orientation.

Read with the orientation as the doublet: every elementary move is an up ↔ down transition. The
same-generation one is a root move (direct); the generation-changing ones are single-wall shifts,
direct through the reference's class and through the node otherwise (`ReferenceRouting`). These are
the charged-current transitions with the CKM's pattern (diagonal, Cabibbo, node-suppressed), and a
flavour change that keeps the doublet member (a neutral one) needs two moves.
-/

namespace PMFlavor.OrientationDoublet

/-- Orientation of a two-wall pair: positive when the wall-`F` class follows the wall-`T` class. -/
def orient (t f : Fin 3) : Bool := decide (f = t + 1)

/-- **Shifting the wall-`F` class to the third class reverses the orientation.** -/
theorem wall_F_shift_flips : ∀ t f f' : Fin 3, t ≠ f → f' ≠ t → f' ≠ f →
    orient t f' = !orient t f := by decide

/-- **Shifting the wall-`T` class to the third class reverses the orientation.** -/
theorem wall_T_shift_flips : ∀ t t' f : Fin 3, t ≠ f → t' ≠ f → t' ≠ t →
    orient t' f = !orient t f := by decide

/-- **The root move by the label exchanges the walls' classes and reverses the orientation.** -/
theorem root_move_flips : ∀ t f : Fin 3, t ≠ f → orient f t = !orient t f := by decide

/-- The generation of a pair is the class it omits. -/
def gen (t f : Fin 3) : Fin 3 := -t - f

/-- **No single move changes the generation and keeps the orientation.** -/
theorem no_neutral_change : ∀ t f t' f' : Fin 3, t ≠ f → t' ≠ f' →
    ((t = t' ∧ f ≠ f') ∨ (f = f' ∧ t ≠ t') ∨ (t' = f ∧ f' = t)) →
    gen t f ≠ gen t' f' → orient t' f' ≠ orient t f := by
  intro t f t' f'
  fin_cases t <;> fin_cases f <;> fin_cases t' <;> fin_cases f' <;> simp [gen, orient]

end PMFlavor.OrientationDoublet
