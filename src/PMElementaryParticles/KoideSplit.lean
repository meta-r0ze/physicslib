import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt

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

Read as a two-outcome record, "is the state generation-symmetric or not",
`Q = 2/3` says that record is a fair coin (`koide_iff_fair`). This is not
the fair flag of `PMAction.ClockLedger`: that flag measures fidelity under the
cyclic shift, and at `Q = 2/3` it is `3/8` (`shiftFlag_at_koide`). So the
clock ledger's `1/2` does not by itself give Koide.

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


/-! ## Koide as a fair binary record -/

/-- Share of the norm in the symmetry-breaking part: the probability that the
state is *not* generation-symmetric (projective two-outcome question). -/
def breakingShare (v : Fin 3 → ℝ) : ℝ := normSq (doublet v) / normSq v

/-- **`Q = 2/3` iff the two-outcome record "symmetric / broken" is a fair coin.** -/
theorem koide_iff_fair (v : Fin 3 → ℝ) (h : total v ≠ 0) :
    koideQ v = 2 / 3 ↔ breakingShare v = 1 / 2 := by
  rw [koide_iff_equal_split v h, breakingShare, normSq_split v]
  have hs : 0 < normSq (singlet v) := by rw [normSq_singlet]; positivity
  have hd : 0 ≤ normSq (doublet v) := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hpos : normSq (singlet v) + normSq (doublet v) ≠ 0 := by linarith
  constructor
  · intro he; rw [he]; field_simp; ring
  · intro hf; field_simp at hf; linarith

/-- Overlap of the state with its cyclic relabelling. -/
def shiftOverlap (v : Fin 3 → ℝ) : ℝ := ∑ i, v i * cyc v i

theorem shiftOverlap_eq (v : Fin 3 → ℝ) :
    shiftOverlap v = (total v ^ 2 - normSq v) / 2 := by
  simp only [shiftOverlap, cyc, total, normSq, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  ring

/-- The fidelity flag of the cyclic relabelling, `(1 − ⟨v, Cv⟩/|v|²)/2`, the
flag measure of `PMAction.ClockLedger` evaluated on the state `v`. -/
def shiftFlag (v : Fin 3 → ℝ) : ℝ := (1 - shiftOverlap v / normSq v) / 2

/-- **At `Q = 2/3` the fidelity flag is `3/8`, not `1/2`.** So the clock ledger's
fair flag (a fixed-point-free shift flags `1/2` averaged over states) is a
different coin from the Koide record. -/
theorem shiftFlag_at_koide (v : Fin 3 → ℝ) (h : total v ≠ 0)
    (hk : koideQ v = 2 / 3) : shiftFlag v = 3 / 8 := by
  have hn : normSq v ≠ 0 := by
    rw [normSq_split]
    have hs : 0 < normSq (singlet v) := by rw [normSq_singlet]; positivity
    have hd : 0 ≤ normSq (doublet v) := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  have hq : normSq v = 2 / 3 * total v ^ 2 := by
    have h2 : total v ^ 2 ≠ 0 := pow_ne_zero 2 h
    rw [koideQ] at hk; field_simp at hk; linarith
  rw [shiftFlag, shiftOverlap_eq, hq]
  have h2 : total v ^ 2 ≠ 0 := pow_ne_zero 2 h
  field_simp
  ring


/-! ## The pair-plus-one limit -/

/-- Two degenerate generations with amplitude `α` and one distinct generation
with amplitude `α + β`. -/
def pairPlusOne (α β : ℝ) : Fin 3 → ℝ := ![α, α, α + β]

theorem pairPlusOne_split (α β : ℝ) :
    normSq (doublet (pairPlusOne α β)) = 2 * β ^ 2 / 3 ∧
      normSq (singlet (pairPlusOne α β)) = (3 * α + β) ^ 2 / 3 := by
  constructor
  · simp only [normSq, doublet, total, pairPlusOne, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · rw [normSq_singlet]
    simp only [total, pairPlusOne, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- **In the pair-plus-one limit, `Q = 2/3` fixes the distinct/pair amplitude
excess:** `β = 3(1 + √2) α`, so the distinct amplitude is `(4 + 3√2) α`. -/
theorem pairPlusOne_koide {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    koideQ (pairPlusOne α β) = 2 / 3 ↔ β = 3 * (1 + Real.sqrt 2) * α := by
  have ht : total (pairPlusOne α β) ≠ 0 := by
    simp only [total, pairPlusOne, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linarith
  rw [koide_iff_equal_split _ ht, (pairPlusOne_split α β).1, (pairPlusOne_split α β).2]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · intro h
    have hsq : (Real.sqrt 2 * β) ^ 2 = (3 * α + β) ^ 2 := by nlinarith
    have hl : Real.sqrt 2 * β = 3 * α + β := by
      have h1 : 0 ≤ Real.sqrt 2 * β := by positivity
      have h3 : 0 ≤ 3 * α + β := by linarith
      nlinarith [sq_nonneg (Real.sqrt 2 * β - (3 * α + β)),
        sq_nonneg (Real.sqrt 2 * β + (3 * α + β))]
    nlinarith
  · intro h
    subst h
    nlinarith

end PMElementaryParticles.KoideSplit

end
