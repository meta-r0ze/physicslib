import PMConstants.VevCorrections

/-!
# Why the VEV's noise divisor is `3`, not `4`

`VevCorrections.divisor_window` leaves two divisors that fit the Fermi window, `3` and `4`: the
temporal noise `Y` shared over the axes other than the reference's, or over all four. Exact repair
of the reference decides between them.

* `share_spatial`: let `share : Fin 4 → ℝ` be the noise residual per lattice axis, axis `0` the
  reference's (time) axis (`RequirementRows.axis_symmetry_kept`). If the reference is repaired
  exactly, its axis keeps no residual (`share 0 = 0`; `RepairBudget`'s exactness premise, which has
  a unitary witness); if the residual is symmetric under the axis permutations that fix the
  reference's axis (`swap 1 2`, `swap 1 3`); and if the shares total `Y`, then every spatial axis
  carries `Y/3`.
* `four_needs_residual`: the divisor-`4` reading (equal shares on all four axes) gives the
  reference's axis `Y/4 ≠ 0`, contradicting exact repair.
* `noise_divisor`: hence the per-axis noise is `Y/3`, and with it the VEV lies in the Fermi window
  (`divisor_window` at `k = 3`).

So the `3` is the number of axes the exact repair does not clean, not a separate choice; that it
coincides with the colour-axis count `σ − χ` is the same fact, since the colour axes are the spatial
ones. The remaining premise is that the VEV reads one axis's share of the residual.
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

/-- **The noise divisor.** -/
theorem noise_divisor :
    (246.21957 < VevCorrections.withDivisor 3 ∧ VevCorrections.withDivisor 3 < 246.21971) ∧
      VevCorrections.Y ≠ 0 :=
  ⟨(VevCorrections.divisor_window 3 (by norm_num)).mpr (Or.inl rfl), by
    rw [VevCorrections.Y_val]; norm_num⟩

end PMConstants.NoiseShare
