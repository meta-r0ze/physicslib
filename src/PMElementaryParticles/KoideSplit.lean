import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Koide ratio as a singlet/doublet split

Three generations carry amplitudes `v : Fin 3 → ℝ` (for masses, `v g = √m_g`).
The cyclic relabelling of the generations (the triality orbit of the three glue
cosets) splits `v` into a symmetric part `singlet v` (all entries equal to the
mean) and the rest `doublet v`. The two parts are orthogonal (`normSq_split`).

The Koide ratio `Q = Σ v² / (Σ v)²` depends only on how the norm divides
between the two parts (`koideQ_eq`):

`Q = 1/3 + |doublet|² / (3 |singlet|²)`.

So `Q = 2/3` exactly when the symmetric part and the symmetry-breaking part
have equal norm (`koide_iff_equal_split`). Both norms, and so `Q`, are
unchanged by a cyclic relabelling of the generations (`koideQ_cyclic`).

This is linear algebra only: no premise and no data.
-/

noncomputable section

namespace PMElementaryParticles.KoideSplit

open scoped BigOperators

/-- Sum of the three amplitudes. -/
def total (v : Fin 3 → ℝ) : ℝ := ∑ i, v i

/-- Squared norm. -/
def normSq (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2

/-- The generation-symmetric part: every entry is the mean. -/
def singlet (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun _ => total v / 3

/-- The symmetry-breaking part. -/
def doublet (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => v i - total v / 3

/-- The Koide ratio `Σ v² / (Σ v)²`. -/
def koideQ (v : Fin 3 → ℝ) : ℝ := normSq v / total v ^ 2

theorem normSq_singlet (v : Fin 3 → ℝ) : normSq (singlet v) = total v ^ 2 / 3 := by
  simp only [normSq, singlet, Fin.sum_univ_three]
  ring

/-- The symmetric part sums to the total; the breaking part sums to zero. -/
theorem total_doublet (v : Fin 3 → ℝ) : total (doublet v) = 0 := by
  simp only [total, doublet, Fin.sum_univ_three]
  ring

/-- The two parts are orthogonal: their norms add. -/
theorem normSq_split (v : Fin 3 → ℝ) :
    normSq v = normSq (singlet v) + normSq (doublet v) := by
  simp only [normSq, singlet, doublet, total, Fin.sum_univ_three]
  ring

/-- **The Koide ratio measures the split.** -/
theorem koideQ_eq (v : Fin 3 → ℝ) (h : total v ≠ 0) :
    koideQ v = 1 / 3 + normSq (doublet v) / (3 * normSq (singlet v)) := by
  rw [koideQ, normSq_split, normSq_singlet]
  have h2 : total v ^ 2 ≠ 0 := pow_ne_zero 2 h
  field_simp

/-- **`Q = 2/3` iff the symmetric and symmetry-breaking parts have equal norm.** -/
theorem koide_iff_equal_split (v : Fin 3 → ℝ) (h : total v ≠ 0) :
    koideQ v = 2 / 3 ↔ normSq (doublet v) = normSq (singlet v) := by
  rw [koideQ_eq v h, normSq_singlet]
  have hs : 0 < total v ^ 2 := by positivity
  constructor
  · intro hq
    field_simp at hq
    linarith
  · intro hd
    rw [hd]
    field_simp
    ring

/-- `Q` lies in `[1/3, 1]` for amplitudes of one sign. The lower end is the fully
symmetric case (no breaking). -/
theorem koideQ_ge (v : Fin 3 → ℝ) (h : total v ≠ 0) : 1 / 3 ≤ koideQ v := by
  rw [koideQ_eq v h]
  have hd : 0 ≤ normSq (doublet v) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hs : 0 < normSq (singlet v) := by
    rw [normSq_singlet]; positivity
  have : 0 ≤ normSq (doublet v) / (3 * normSq (singlet v)) := by positivity
  linarith

/-- Cyclic relabelling of the three generations. -/
def cyc (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => v (i + 1)

theorem total_cyc (v : Fin 3 → ℝ) : total (cyc v) = total v := by
  simp only [total, cyc, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  ring

theorem normSq_cyc (v : Fin 3 → ℝ) : normSq (cyc v) = normSq v := by
  simp only [normSq, cyc, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  ring

/-- **The split, and so `Q`, does not depend on which coset is called first.** -/
theorem koideQ_cyclic (v : Fin 3 → ℝ) : koideQ (cyc v) = koideQ v := by
  rw [koideQ, koideQ, total_cyc, normSq_cyc]

end PMElementaryParticles.KoideSplit

end
