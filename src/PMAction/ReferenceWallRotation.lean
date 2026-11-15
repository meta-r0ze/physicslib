import PMAction.ReferenceWallMass

/-!
# On the reference's wall the persistence rotation is suppressed by the hierarchy

`ReferenceWallMass`: the light mass is `M = D_R X`, `D_R = diag(d)` (the reference-wall carriers of
each label class over `y`) and `X = δ_O · 1 + cyc κ_O` (the other wall's detuning and carriers). The
rows of `M` are the reference's wall (wall `false`, the wall the charged current acts on), so the
persistence states on that wall are the eigenvectors of `M Mᴴ`.

* `left_gram`: `M Mᴴ = D_R (X Xᴴ) D_Rᴴ`.
* `cyc_gram_offdiag`: `cyc κ (cyc κ)ᴴ` is diagonal (the rows of a cyclic shift have disjoint
  supports).
* `left_gram_entry`: for `i ≠ j`, `(M Mᴴ)ᵢⱼ = dᵢ (δ̄ (cyc κ)ᵢⱼ + δ conj (cyc κ)ⱼᵢ) d̄ⱼ`. The second-order
  carrier term does not reach the off-diagonal; every off-diagonal entry is first order in
  `κ_O/δ_O` and carries the factor `dᵢ d̄ⱼ`.

**Reading (first-order perturbation, outside Lean).** The diagonal is `|dᵢ|² (|δ|² + |κ|²)`, so when
`|dᵢ| ≪ |dⱼ|` the rotation angle between label states `i` and `j` on the reference's wall is about
`|dᵢ/dⱼ| · |κ_O/δ_O|`: the ratio of the two label states' masses (at `δ_O` dominant the masses are
`|δ_O dᵢ|`) times the other wall's carrier-to-detuning ratio. The rotation on the other wall
(`Mᴴ M = Xᴴ |D_R|² X`) has no such factor. So if the charged current's persisting states are those
of the wall it acts on, `U` in PMFlavor's `U_uᴴ J U_d` is close to `1` wherever the label states'
masses are hierarchical, whatever `δ_O` is (given `|κ_O| ≲ |δ_O|`). For two label states with
comparable `|dᵢ|` there is no suppression. The premise that the event reads the reference-wall side
is stated here, not derived.
-/

noncomputable section
namespace PMAction.ReferenceWallRotation
open Matrix PMAction.CyclicSeesaw

/-- **The reference-wall Gram matrix.** -/
theorem left_gram (d : Fin 3 → ℂ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    (diagonal d * X) * (diagonal d * X)ᴴ = diagonal d * (X * Xᴴ) * diagonal (star d) := by
  rw [conjTranspose_mul, diagonal_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- **A cyclic shift times its adjoint is diagonal.** -/
theorem cyc_gram_offdiag (κ : Fin 3 → ℂ) (i j : Fin 3) (h : i ≠ j) :
    (cyc κ * (cyc κ)ᴴ) i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [cyc, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]

/-- Off-diagonal entries of `X Xᴴ` for `X = δ · 1 + cyc κ`. -/
theorem x_gram_offdiag (δ : ℂ) (κ : Fin 3 → ℂ) (i j : Fin 3) (h : i ≠ j) :
    ((δ • (1 : Matrix (Fin 3) (Fin 3) ℂ) + cyc κ) * (δ • 1 + cyc κ)ᴴ) i j =
      star δ * cyc κ i j + δ * star (cyc κ j i) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [cyc, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] <;> ring

/-- **Off-diagonal entries of `M Mᴴ` carry `dᵢ d̄ⱼ` and are first order in the carriers.** -/
theorem left_gram_entry (d : Fin 3 → ℂ) (δ : ℂ) (κ : Fin 3 → ℂ) (i j : Fin 3) (h : i ≠ j) :
    ((diagonal d * (δ • 1 + cyc κ)) * (diagonal d * (δ • 1 + cyc κ))ᴴ) i j =
      d i * (star δ * cyc κ i j + δ * star (cyc κ j i)) * star (d j) := by
  rw [left_gram, Matrix.mul_diagonal, Matrix.diagonal_mul, x_gram_offdiag δ κ i j h, Pi.star_apply]

end PMAction.ReferenceWallRotation
