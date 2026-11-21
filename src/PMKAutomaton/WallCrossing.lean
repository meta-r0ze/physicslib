import PMKAutomaton.ClockAlignment

/-!
# Glue cosets are wall-crossing steps

`ClockAlignment` computes the `D4` glue key

`glueKey r = ((<r,a> + <r,c>) mod 2, (<r,a> + <r,beta>) mod 2)`

and the clock signatures of its three nonzero cosets. In
`ControlledGluedRegister.wallClass`, generation `g` has the two wall classes
other than `g`. This module proves that the roots moving between those two
walls are exactly coset `g`.

The key facts are `glueKey_add`, `moves_iff` and `wall_crossing_filter`. The
three concrete pairs are `generation_vector_crossing`,
`generation_spinor_crossing` and `generation_conjugateSpinor_crossing`, each
with the clock signature of its coset.

The identification of the sixteen channels with the internal `D4` remains a
named placement premise; the step-to-cost rule remains open.
-/

namespace PMKAutomaton.WallCrossing

open PMKAutomaton.ClockRing
open PMKAutomaton.ClockAlignment

abbrev Key := ZMod 2 × ZMod 2

/-- Every key is its own negative in `ZMod 2 × ZMod 2`. -/
theorem key_add_self : ∀ k : Key, k + k = 0 := by
  decide

/-- The sum of two distinct nonzero keys is nonzero and differs from both. -/
theorem key_add_distinct :
    ∀ x y : Key, x ≠ 0 → y ≠ 0 → x ≠ y →
      x + y ≠ 0 ∧ x + y ≠ x ∧ x + y ≠ y := by
  decide

/-- With three distinct nonzero keys, the third is the sum of the other two. -/
theorem third_key_add :
    ∀ g x y : Key, g ≠ 0 → x ≠ 0 → y ≠ 0 → g ≠ x → g ≠ y → x ≠ y →
      x + y = g := by
  decide

/-- Adding a root adds its glue key. -/
theorem glueKey_add' (z r : V) :
    glueKey (z + r) = glueKey z + glueKey r :=
  glueKey_add z r

/-- A root moves a vector from key `x` to key `y` exactly when the root lies in
the coset `x + y`. -/
theorem moves_iff (z r : V) (x y : Key) (hx : glueKey z = x) :
    glueKey (z + r) = y ↔ glueKey r = x + y := by
  rw [glueKey_add', hx]
  constructor
  · intro h
    rw [← h, ← add_assoc, key_add_self, zero_add]
  · intro h
    rw [h, ← add_assoc, key_add_self, zero_add]

/-- **The roots moving from key `x` to key `y` are the coset `x + y`.** -/
theorem wall_crossing_filter (x y : Key) (z : V) (hx : glueKey z = x) :
    (rootList.filter fun r => glueKey (z + r) = y) = rootsOfKey (x + y) := by
  unfold rootsOfKey
  apply List.filter_congr
  intro r _
  rw [decide_eq_decide]
  exact moves_iff z r x y hx

/-- Generation 0 (vector walls): moving between the spinor and
conjugate-spinor walls uses the vector coset `(0,1)`, whose clock signature is
seven forward, seven backward and two silent roots. -/
theorem generation_vector_crossing (z : V) (hz : glueKey z = (1, 1)) :
    (rootList.filter fun r => glueKey (z + r) = (1, 0)) = rootsOfKey (0, 1) ∧
      ((rootsOfKey (0, 1)).filter fun r => clockReading r = 1).length = 7 ∧
      ((rootsOfKey (0, 1)).filter fun r => clockReading r = -1).length = 7 ∧
      ((rootsOfKey (0, 1)).filter fun r => clockReading r = 0).length = 2 := by
  have hsum : ((1, 1) : Key) + (1, 0) = (0, 1) := by decide
  refine ⟨?_, vectorRoots_counts.1, vectorRoots_counts.2.1,
    vectorRoots_counts.2.2⟩
  simpa [hsum] using wall_crossing_filter (1, 1) (1, 0) z hz

/-- Generation 1 (spinor walls): moving between the vector and
conjugate-spinor walls uses the spinor coset `(1,1)`, whose clock signature is
four forward, four backward and no silent roots. -/
theorem generation_spinor_crossing (z : V) (hz : glueKey z = (0, 1)) :
    (rootList.filter fun r => glueKey (z + r) = (1, 0)) = rootsOfKey (1, 1) ∧
      ((rootsOfKey (1, 1)).filter fun r => clockReading r = 1).length = 4 ∧
      ((rootsOfKey (1, 1)).filter fun r => clockReading r = -1).length = 4 ∧
      ((rootsOfKey (1, 1)).filter fun r => clockReading r = 0).length = 0 := by
  have hsum : ((0, 1) : Key) + (1, 0) = (1, 1) := by decide
  refine ⟨?_, spinorRoots_counts.1, spinorRoots_counts.2.1,
    spinorRoots_counts.2.2⟩
  simpa [hsum] using wall_crossing_filter (0, 1) (1, 0) z hz

/-- Generation 2 (conjugate-spinor walls): moving between the vector and
spinor walls uses the conjugate-spinor coset `(1,0)`, whose clock signature is
four forward, four backward and eight silent roots. -/
theorem generation_conjugateSpinor_crossing (z : V) (hz : glueKey z = (0, 1)) :
    (rootList.filter fun r => glueKey (z + r) = (1, 1)) = rootsOfKey (1, 0) ∧
      ((rootsOfKey (1, 0)).filter fun r => clockReading r = 1).length = 4 ∧
      ((rootsOfKey (1, 0)).filter fun r => clockReading r = -1).length = 4 ∧
      ((rootsOfKey (1, 0)).filter fun r => clockReading r = 0).length = 8 := by
  have hsum : ((0, 1) : Key) + (1, 1) = (1, 0) := by decide
  refine ⟨?_, conjugateSpinorRoots_counts.1,
    conjugateSpinorRoots_counts.2.1, conjugateSpinorRoots_counts.2.2⟩
  simpa [hsum] using wall_crossing_filter (0, 1) (1, 1) z hz

end PMKAutomaton.WallCrossing
