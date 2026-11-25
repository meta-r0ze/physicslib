import PMConstants.VevCorrections

/-!
# The noise share after exact repair

Axis zero is the reference's time axis (`RequirementRows.axis_symmetry_kept`).
If exact repair clears its residual, and the other axis shares are symmetric
and total `Y`, each spatial axis carries `Y/3`. An equal share on all four
axes gives the reference axis a residual whenever `Y ≠ 0`.
-/

noncomputable section
namespace PMConstants.NoiseShare
open PMConstants

/-- **Exact repair leaves the noise on the three spatial axes, `Y/3` each.** -/
theorem share_spatial (share : Fin 4 → ℝ) (Y : ℝ) (hexact : share 0 = 0)
    (h12 : share 1 = share 2) (h13 : share 1 = share 3) (hsum : ∑ i, share i = Y) :
    ∀ i : Fin 4, i ≠ 0 → share i = Y / 3 := by
  rw [Fin.sum_univ_four] at hsum
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  all_goals (simp only [Fin.mk_one, Fin.reduceFinMk]; linarith)

/-- The symmetry hypotheses are the permutations that fix the reference's axis. -/
theorem symmetric_of_invariant (share : Fin 4 → ℝ)
    (hinv : ∀ σ : Equiv.Perm (Fin 4), σ 0 = 0 → ∀ i, share (σ i) = share i) :
    share 1 = share 2 ∧ share 1 = share 3 := by
  constructor
  · have := hinv (Equiv.swap 1 2) (by decide) 1
    simpa [Equiv.swap_apply_left] using this.symm
  · have := hinv (Equiv.swap 1 3) (by decide) 1
    simpa [Equiv.swap_apply_left] using this.symm

/-- **Equal shares on all four axes put residual on the reference.** -/
theorem four_needs_residual (Y : ℝ) (hY : Y ≠ 0) (share : Fin 4 → ℝ)
    (hall : ∀ i, share i = Y / 4) : share 0 ≠ 0 := by
  rw [hall]; intro h; apply hY; linarith

end PMConstants.NoiseShare
