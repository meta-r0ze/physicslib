import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import PersistenceMechanics.LawSelection

/-! **Experimental/candidate module.**

# Finite channel measure

A channel-counting measure on an arbitrary finite label type. 
The measure is normalized by the total weight; no
continuum measure is assumed.
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

/-- **The counting measure is the persistence-selected uniform law.** Equal channel weights give
`probability m = 1/|ι|`, which is exactly `LawSelection.uniform` — the unique law minimizing the
long-run cost rate (`LawSelection.averageRate_eq_iff`, `LawSelection.uniform_law`). So *which*
probability law the channels carry is selected by persistence; only the *weights* (which channels)
remain. -/
theorem probability_uniform_of_const_weight (m : ChannelMeasure ι) (hw : ∀ i, m.weight i = 1) :
    probability m = LawSelection.uniform := by
  funext i
  have htot : total m = (Fintype.card ι : ℝ) := by simp [total, hw]
  simp [probability, htot, LawSelection.uniform, hw]

/-- **Closure forces the counting measure.** A channel probability invariant under every relabeling
of the labels is uniform — the same Closure argument as
`PMSubstrate.ClosureSymmetry.invariant_measure_uniform`, here on the finite channel set. -/
theorem probability_perm_uniform [DecidableEq ι] (m : ChannelMeasure ι) (h : total m ≠ 0)
    (hinv : ∀ σ : Equiv.Perm ι, ∀ a, probability m (σ a) = probability m a) (a : ι) :
    probability m a = 1 / Fintype.card ι := by
  have : Nonempty ι := ⟨a⟩
  have hsum := probability_sum m h
  have hall : ∀ b, probability m b = probability m a := by
    intro b
    have hh := hinv (Equiv.swap a b) a
    rwa [Equiv.swap_apply_left] at hh
  have hconst : ∑ b, probability m b = (Fintype.card ι : ℝ) * probability m a := by
    rw [Finset.sum_congr rfl (fun b _ => hall b), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hsum] at hconst
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eq_div_iff hc, mul_comm]
  exact hconst.symm

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
