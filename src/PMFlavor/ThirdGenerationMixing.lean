import PMFlavor.LinkFlux

/-!
# A conserving network does not mix its heaviest generation

`LinkFlux.kronLink_zero_mode`: every real-leg reduced link annihilates `(1, 1, 1)`. This module
asks what that does to the mixing, and so whether picture B's amplitudes (`VubSeriesPath`,
`KronSeries`) can be eigenvector mixings.

**The mixing is the eigenvector overlap, exactly.** The on-site mass is flavour-blind
(`PMAction.WallExchange`: `δβ ⊗ 1`), so for Hermitian `Y` the two-wall Hamiltonian is block
diagonal in `Y`'s eigenbasis and the flavour eigenvectors of `Y` are exact (not only in the
seesaw limit). The mixing matrix is the overlap of the two sectors' eigenvectors.

* `nonzero_mode_sumzero`: an eigenvector of a real conserving link with nonzero eigenvalue sums to
  zero (the columns sum to zero).
* `zero_mode_unmixed`: so `(1, 1, 1)` has zero overlap with every nonzero mode of any other real
  conserving link. Two sectors on real conserving networks share their heaviest state
  (`WallSeesaw`: zero `σ`), and its row and column of the mixing matrix are `(1, 0, 0)`:
  `|V_tb| = 1`, `V_ub = V_cb = V_td = V_ts = 0`.
* Contrast (numerical, outside Lean): a conserving down link against a diagonal up link gives a
  democratic column, all entries `1/√3`, excluded by data.

So among the network readings, both sectors conserving is the one that matches the data's
leading order (`|V_tb| ≈ 1`, small third-generation mixings), and in it picture B's
`|V_ub| = 1/(2α⁻¹ + π)` cannot be an eigenvector overlap: it must be a first-order effect of
whatever lifts the shared zero mode differently in the two sectors (a flux, `LinkFlux`, or a
non-conserving leak). To first order such a term `P` mixes the zero mode `w` with mode `k` by
`⟨v_k, P w⟩ / λ_k`, so the gaps matter:

* `in_cycle_spectrum`: for legs `a` on the vector (in-cycle) class and `b` on both node classes,
  the reduced link has eigenvalues `0` on `(1, 1, 1)`, `3b/2` on `(2, −1, −1)` (the generation
  whose two classes are both node classes) and `a + b/2` on `(0, 1, −1)` (the in-cycle pair).
  With `b = α` (`VubSeriesPath`) the first gap is `3α/2`, small; the second is of order the
  in-cycle leg.
-/

noncomputable section
namespace PMFlavor.ThirdGenerationMixing
open Matrix LinkKronComparison LinkFlux

/-- **A nonzero mode of a conserving link sums to zero.** -/
theorem nonzero_mode_sumzero (a b c lam : ℝ) (v : Fin 3 → ℝ)
    (h : kronLink a b c *ᵥ v = lam • v) (hl : lam ≠ 0) : v 0 + v 1 + v 2 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [kronLink, mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  have hs : lam * (v 0 + v 1 + v 2) = 0 := by linear_combination -(h0 + h1 + h2)
  exact (mul_eq_zero.mp hs).resolve_left hl

/-- **The shared zero mode does not mix.** Its overlap with every nonzero mode of another real
conserving link vanishes. -/
theorem zero_mode_unmixed (a b c a' b' c' lam : ℝ) (v : Fin 3 → ℝ)
    (h : kronLink a' b' c' *ᵥ v = lam • v) (hl : lam ≠ 0) :
    kronLink a b c *ᵥ ![1, 1, 1] = 0 ∧ (![1, 1, 1] ⬝ᵥ v : ℝ) = 0 := by
  refine ⟨kronLink_zero_mode a b c, ?_⟩
  have hs := nonzero_mode_sumzero a' b' c' lam v h hl
  simpa [dotProduct, Fin.sum_univ_three] using hs

/-- **The spectrum with equal node legs.** Legs `a` on the vector class (`0`), `b` on both node
classes: eigenvalues `3b/2` on `(2, −1, −1)` and `a + b/2` on `(0, 1, −1)`, besides `0` on
`(1, 1, 1)`. -/
theorem in_cycle_spectrum (a b : ℝ) :
    kronLink a b b *ᵥ ![2, -1, -1] = (3 * b / 2) • ![2, -1, -1] ∧
      kronLink a b b *ᵥ ![0, 1, -1] = (a + b / 2) • ![0, 1, -1] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [kronLink, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end PMFlavor.ThirdGenerationMixing
