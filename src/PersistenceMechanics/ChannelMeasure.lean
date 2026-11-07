import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Finite channel measure

A generic E8 channel-counting measure on a finite label type.  The measure is
normalized by the total weight; no continuum measure is assumed.
-/

noncomputable section
namespace PersistenceMechanics.ChannelCounting

open Finset

variable {ι : Type*} [Fintype ι]

/-- A finite channel measure. -/
structure ChannelMeasure (ι : Type*) [Fintype ι] where
  weight : ι → ℝ

def total (m : ChannelMeasure ι) : ℝ :=
  ∑ i, m.weight i

def probability (m : ChannelMeasure ι) (i : ι) : ℝ :=
  m.weight i / total m

theorem probability_sum (m : ChannelMeasure ι) (h : total m ≠ 0) :
    ∑ i, probability m i = 1 := by
  unfold probability total
  rw [← Finset.sum_div]
  exact div_self h

theorem probability_nonneg (m : ChannelMeasure ι) (h : ∀ i, 0 ≤ m.weight i) (i : ι) :
    0 ≤ probability m i := by
  unfold probability total
  exact div_nonneg (h i) (Finset.sum_nonneg (by intro j _; exact h j))

/-- Probability of a selected subset of modes. -/
def subsetProbability (m : ChannelMeasure ι) (S : Finset ι) : ℝ :=
  S.sum m.weight / total m

theorem subsetProbability_nonneg (m : ChannelMeasure ι)
    (h : ∀ i, 0 ≤ m.weight i) (S : Finset ι) :
    0 ≤ subsetProbability m S := by
  unfold subsetProbability total
  exact div_nonneg (Finset.sum_nonneg (by intro i _; exact h i))
    (Finset.sum_nonneg (by intro i _; exact h i))

end PersistenceMechanics.ChannelCounting
