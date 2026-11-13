import PMConstants.VevLedger
import PMConstants.WeakConfinement

/-!
# The VEV's noise divisor is the three spatial axes

`VevCorrections.divisor_window`: the Fermi window allows the noise divisor `3` or `4`, and the
paper reads `3` as "the noise lands on the axes orthogonal to the reference". That reading is now
constrained.

The margin noise `Y` (Paper I's margin, `ElectroweakE8.bareYukawa`) is spread over the four axes by
a share `s : Fin 4 → ℝ`.

* **Time carries none.** The reference sits on the time axis (`RequirementRows.axis_symmetry_kept`),
  and weak refreshes the clock row, which its events reach every tick
  (`WeakConfinement.weakReach_iff`, `WeakLocality.weak_covers_iff`). Noise on the time axis is
  removed by that refresh, so `s 0 = 0`.
* **The spatial axes are equivalent.** The axis permutations that fix time are the kept symmetry
  (the same group as `axis_symmetry_kept`), so the share is invariant under them.
* `noise_share`: then each spatial axis carries exactly `Y/3`, and `3 = σ − χ = D − 1`
  (`VevLedger.noiseDenominator_eq_orthogonal`). The divisor `4` would put noise on the time axis,
  which the clock refresh removes.

What remains a reading is that the VEV's margin factor is one axis's share, `1 − Y/3`.
-/

noncomputable section
namespace PMConstants.VevNoise

/-- **Each spatial axis carries a third of the noise.** -/
theorem noise_share (s : Fin 4 → ℝ) (Y : ℝ) (htime : s 0 = 0)
    (hsym : ∀ σ : Equiv.Perm (Fin 4), σ 0 = 0 → ∀ μ, s (σ μ) = s μ)
    (htotal : ∑ μ, s μ = Y) : ∀ μ, μ ≠ 0 → s μ = Y / 3 := by
  have h12 : s 2 = s 1 := by
    have := hsym (Equiv.swap 1 2) (by decide) 1
    simpa using this
  have h13 : s 3 = s 1 := by
    have := hsym (Equiv.swap 1 3) (by decide) 1
    simpa using this
  rw [Fin.sum_univ_four, htime, h12, h13] at htotal
  intro μ hμ
  fin_cases μ
  · exact absurd rfl hμ
  · show s 1 = Y / 3; linarith
  · show s 2 = Y / 3; rw [h12]; linarith
  · show s 3 = Y / 3; rw [h13]; linarith

/-- **The divisor is the number of spatial axes.** -/
theorem divisor_is_spatial :
    PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi = PMSubstrate.E8Values.D - 1 ∧
      PMSubstrate.E8Values.D - 1 = 3 :=
  ⟨VevLedger.noiseDenominator_eq_orthogonal, by rw [PMSubstrate.E8Values.D_eq]⟩

end PMConstants.VevNoise
