import PMAction.NativeExternal

/-!
# The confined carrier's axial current is the on-site spin

`NativeExternal`: the native current operators are the density `1` and the velocities `αⱼ`, and the
weak vertex is `u† J^μ P_L w` with `P_L = (1 − Γ)/2` (`native_current`). So the weak axial current is
`J^μ Γ`, on each wall (the charged projector's chirality is `Γ` on both walls,
`WallChiralCurrent.chirality`).

* `alpha_gamma`: `αⱼ Γ = Σⱼ`, the on-site spin `Σⱼ = −i α_{j+1} α_{j+2}`. So the spatial axial current
  is the on-site spin operator (`axial_is_spin`), and the vertex splits as vector minus axial,
  `u† J^μ P_L w = ½ (u† J^μ w − u† J^μ Γ w)` (`vertex_split`).
* `slice_not_chirality`: the slice sign `diag(1, −1)` (the two D4 slices rotated oppositely, the
  domain-wall axial rotation of `tools/slice_axial.py`) is not the charged chirality. Its conserved
  link current is a different operator: it is exactly normalized for a free carrier but leaks `O(1)`
  at the two-slice wall, and it is not the current the weak vertex reads.

**Numerically** (`tools/slice_axial.py`, spin-up ground doublet of the confined carrier on `n³`
cubes): the weak axial charge `⟨Σ_z⟩` is `0.826, 0.759, 0.717, 0.692` for `n = 3…6`, tending to about
`0.65` (the MIT-bag value), while the slice current gives `0.22–0.40`. The pion source is the same
operator (its divergence, through PCAC). The carrier's size, and so the value of `⟨Σ_z⟩`, is the
carrier level and radius certificate (PMAction REVIEW) and PMHadrons' calculation.
-/

noncomputable section
namespace PMAction.ConfinedAxialCurrent
open Matrix ConcreteFermion

/-- On-site spin `Σⱼ = −i α_{j+1} α_{j+2}`. -/
def Sigma : Fin 3 → Spin := fun j => -Complex.I • (alpha (j + 1) * alpha (j + 2))

theorem alpha_gamma : ∀ j, alpha j * gamma = Sigma j := by
  intro j
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Sigma, alpha, gamma, mul_apply, Fin.sum_univ_four]

/-- **The weak axial current's spatial part is the on-site spin.** -/
theorem axial_is_spin (j : Fin 3) : NativeExternal.J j.succ * gamma = Sigma j := by
  rw [← alpha_gamma]
  fin_cases j <;> rfl

/-- **The vertex is vector minus axial**, with axial current `J^μ Γ`. -/
theorem vertex_split (μ : Fin 4) (u w : Fin 4 → ℂ) :
    star u ⬝ᵥ ((NativeExternal.J μ * WeakVertex.PL) *ᵥ w) =
      (1 / 2 : ℂ) * (star u ⬝ᵥ (NativeExternal.J μ *ᵥ w) -
        star u ⬝ᵥ ((NativeExternal.J μ * gamma) *ᵥ w)) := by
  have hPL : WeakVertex.PL = (1 / 2 : ℂ) • ((1 : Spin) - gamma) := by
    rw [WeakVertex.PL, VATrace.L_eq]
  rw [hPL, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, smul_mulVec, sub_mulVec,
    dotProduct_smul, dotProduct_sub, smul_eq_mul, ← mulVec_mulVec]

/-- The slice sign on the two D4 slices. -/
def sliceSign : Matrix Sites Sites ℂ := fromBlocks 1 0 0 (-1)

theorem slice_not_chirality : sliceSign ≠ WallChiralCurrent.chirality := by
  intro h
  have := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
  simp [sliceSign, WallChiralCurrent.chirality, gamma] at this
  norm_num at this

end PMAction.ConfinedAxialCurrent
