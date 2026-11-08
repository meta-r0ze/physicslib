import PMConstants.Allocation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Clock credit and maximal uniform regulation

A normalized credit invariant under the actual cyclic update is uniform. One
unit across 43 phases gives 1/43. Equal regulatory gain on 23 intrinsic labels,
with a total budget of 3, then bounds the gain by 128/989. The largest feasible
gain attains that bound. Feasibility or a positive restoring gain alone does not
force saturation. Maximizing regulatory margin is an explicit objective.
-/

namespace PMConstants.RegulatoryBudget
open Finset

theorem cyclic_uniform {N : ℕ} [NeZero N] (credit : Fin N → ℝ)
    (hinv : ∀ i, credit (finRotate N i) = credit i)
    (hsum : ∑ i, credit i = 1) (i : Fin N) : credit i = 1/N := by
  have hit : ∀ t : ℕ, ∀ j : Fin N, credit (((finRotate N)^[t]) j) = credit j := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => intro j; rw [Function.iterate_succ_apply', hinv, ih]
  have hconst : ∀ j : Fin N, credit j = credit 0 := by
    intro j
    have hj : ((finRotate N)^[j.val]) 0 = j := by
      rw [← finCycle_eq_finRotate_iterate (k := j)]
      simp
    rw [← hj]
    exact hit j.val 0
  have hcount : (N : ℝ) * credit 0 = 1 := by
    simpa [hconst] using hsum
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [hconst i, eq_div_iff hN, mul_comm]
  exact hcount

theorem clock_credit (credit : Fin PMSubstrate.E8Values.Delta → ℝ)
    (hinv : ∀ i, credit (finRotate PMSubstrate.E8Values.Delta i) = credit i)
    (hsum : ∑ i, credit i = 1) : credit 0 = 1/43 :=
  cyclic_uniform credit hinv hsum 0

theorem directional_credit (credit : Fin 4 → ℝ)
    (hinv : ∀ i, credit (finRotate 4 i) = credit i)
    (hsum : ∑ i, credit i = 1) : credit 0 = 1/4 :=
  cyclic_uniform credit hinv hsum 0

def Feasible (labels budget sync gain : ℝ) : Prop :=
  0 ≤ gain ∧ labels*gain+sync ≤ budget

def Maximal (labels budget sync gain : ℝ) : Prop :=
  Feasible labels budget sync gain ∧
    ∀ g, Feasible labels budget sync g → g ≤ gain

theorem feasible_iff {labels budget sync gain : ℝ} (hL : 0 < labels) :
    Feasible labels budget sync gain ↔
      0 ≤ gain ∧ gain ≤ (budget-sync)/labels := by
  unfold Feasible
  rw [le_div_iff₀ hL]
  constructor
  · rintro ⟨hg, hb⟩; exact ⟨hg, by nlinarith⟩
  · rintro ⟨hg, hb⟩; exact ⟨hg, by nlinarith⟩

theorem maximal_iff {labels budget sync gain : ℝ} (hL : 0 < labels)
    (hB : sync ≤ budget) :
    Maximal labels budget sync gain ↔ gain = (budget-sync)/labels := by
  have hpos : 0 ≤ (budget-sync)/labels := div_nonneg (sub_nonneg.mpr hB) hL.le
  have hcap : Feasible labels budget sync ((budget-sync)/labels) :=
    (feasible_iff hL).mpr ⟨hpos, le_rfl⟩
  constructor
  · rintro ⟨hf, hm⟩
    exact le_antisymm ((feasible_iff hL).mp hf).2 (hm _ hcap)
  · rintro rfl
    exact ⟨hcap, fun g hg => ((feasible_iff hL).mp hg).2⟩

theorem scalar_feasible_iff (gain : ℝ) :
    Feasible 23 3 (1/43) gain ↔ 0 ≤ gain ∧ gain ≤ selfCoupling := by
  have hsc : selfCoupling = (3 - 1/43)/23 := by norm_num [selfCoupling]
  simpa [hsc] using (feasible_iff (gain := gain) (budget := 3)
    (sync := 1/43) (show (0 : ℝ) < 23 by norm_num))

theorem scalar_maximal_iff (gain : ℝ) :
    Maximal 23 3 (1/43) gain ↔ gain = selfCoupling := by
  have hsc : selfCoupling = (3 - 1/43)/23 := by norm_num [selfCoupling]
  simpa [hsc] using (maximal_iff (gain := gain) (budget := 3)
    (sync := 1/43) (show (0 : ℝ) < 23 by norm_num) (by norm_num))

/-- There is a positive, solvent alternative to the maximal gain. The queue
or capacity constraints do not by themselves establish maximality. -/
theorem positive_feasible_not_unique :
    Feasible 23 3 (1/43) (selfCoupling/2) ∧
      0 < selfCoupling/2 ∧ selfCoupling/2 < selfCoupling := by
  have h := self_coupling_pos
  refine ⟨(scalar_feasible_iff _).mpr ⟨by linarith, by linarith⟩,
    by linarith, by linarith⟩

end PMConstants.RegulatoryBudget
