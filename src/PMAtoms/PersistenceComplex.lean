import PMAtoms.NeutronPrediction
import PMSubstrate.Impedance
import Mathlib.Tactic

/-!
# The nucleus as one persistence complex

The packing, closure and alpha layers of the nuclear ledger were built as separate formulas.
They are counts of one object: the cubic packing complex (vertices = nucleons, edges = links,
squares, cubes), continued to non-cubic `A` by `n = A^{1/3}`.

* `packingFaces`, `packingCells`: the square and cube counts, `3A − 6A^{2/3} + 3A^{1/3}` and
  `A − 3A^{2/3} + 3A^{1/3} − 1`; at `A = n³` they are `3n(n−1)²` and `(n−1)³`
  (`packingFaces_cube`, `packingCells_cube`).
* `packing_euler`: `V − E + F − C = 1` for every `A`. The complex is contractible.
* `packingClosureRank_eq_faces_sub_cells`: the closure layer's cycle rank `E − V + 1` is
  `F − C`. So nucleons, links and closures are the f-vector of one complex.

The surviving-phase factors are the substrate's Governor rule (`PMSubstrate.governorTerm`: a
credit spread over the `Δ` clock slots) with different credits:

* `phaseMargin_eq_one_add_governor`: the beta margin `41/43` is `1 + governorTerm` (credit `χ`).
* `alphaPhaseFraction_eq_governor`: the alpha suppression is `1 − gap/Δ` (credit = isospin
  gap).
* `neutronMargin_eq_phaseMargin`: the neutron margin is the same `41/43`.
-/

noncomputable section
namespace PMAtoms

/-! ## The f-vector of the packing complex -/

/-- Squares of the cubic packing, continued in `A`: `3A − 6A^{2/3} + 3A^{1/3}`. -/
def packingFaces (a : Nat) : ℝ :=
  3 * (a : ℝ) - 6 * (a : ℝ) ^ ((2 : ℝ) / 3) + 3 * (a : ℝ) ^ ((1 : ℝ) / 3)

/-- Cubes of the cubic packing, continued in `A`: `A − 3A^{2/3} + 3A^{1/3} − 1`. -/
def packingCells (a : Nat) : ℝ :=
  (a : ℝ) - 3 * (a : ℝ) ^ ((2 : ℝ) / 3) + 3 * (a : ℝ) ^ ((1 : ℝ) / 3) - 1

/-- **Euler characteristic.** `V − E + F − C = 1` for every `A`. -/
theorem packing_euler (a : Nat) :
    (a : ℝ) - packingLinks a + packingFaces a - packingCells a = 1 := by
  unfold packingLinks packingFaces packingCells; ring

/-- The closure layer's cycle rank is `E − V + 1`. -/
theorem packingClosureRank_eq_links (a : Nat) :
    packingClosureRank a = packingLinks a - (a : ℝ) + 1 := by
  unfold packingClosureRank packingLinks; ring

/-- **Closures are faces minus cells.** -/
theorem packingClosureRank_eq_faces_sub_cells (a : Nat) :
    packingClosureRank a = packingFaces a - packingCells a := by
  unfold packingClosureRank packingFaces packingCells; ring

lemma cube_rpow_two (n : Nat) :
    ((n ^ 3 : Nat) : ℝ) ^ ((2 : ℝ) / 3) = (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) ≤ n := by positivity
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn']
  norm_num

lemma cube_rpow_one (n : Nat) :
    ((n ^ 3 : Nat) : ℝ) ^ ((1 : ℝ) / 3) = (n : ℝ) := by
  have hn' : (0 : ℝ) ≤ n := by positivity
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn']
  norm_num

theorem packingFaces_cube (n : Nat) :
    packingFaces (n ^ 3) = 3 * (n : ℝ) * ((n : ℝ) - 1) ^ 2 := by
  unfold packingFaces
  rw [cube_rpow_two, cube_rpow_one]; push_cast; ring

theorem packingCells_cube (n : Nat) :
    packingCells (n ^ 3) = ((n : ℝ) - 1) ^ 3 := by
  unfold packingCells
  rw [cube_rpow_two, cube_rpow_one]; push_cast; ring

/-! ## Surviving phases are the Governor rule -/

/-- **The beta margin is `1 + Governor`.** -/
theorem phaseMargin_eq_one_add_governor :
    PMSubstrate.E8Margin.phaseMargin = 1 + PMSubstrate.governorTerm PMSubstrate.baseline := by
  rw [PMSubstrate.E8Margin.phaseMargin_eq]
  norm_num [PMSubstrate.governorTerm, PMSubstrate.baseline]

/-- **The alpha suppression is the Governor rule with the isospin gap as credit.** -/
theorem alphaPhaseFraction_eq_governor (gap : Nat) (h : gap ≤ Δ) :
    alphaPhaseFraction gap = 1 - (gap : ℝ) / (Δ : ℝ) := by
  rw [alphaPhaseFraction_eq gap h, Nat.cast_sub h]
  have : (Δ : ℝ) ≠ 0 := by norm_num [Δ, PMSubstrate.E8Values.Delta]
  field_simp

/-- **The neutron margin is the substrate phase margin.** -/
theorem neutronMargin_eq_phaseMargin :
    neutronMarginFactor = PMSubstrate.E8Margin.phaseMargin := by
  rw [neutronMarginFactor_eq, PMSubstrate.E8Margin.phaseMargin_eq]

end PMAtoms
