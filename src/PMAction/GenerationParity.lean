import PMAction.GenerationWalls
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Within one convention the wall crossing is one-directional, so it is not Hermitian

Step 5 of the generation sector (`PMAction/TODO.md`). `PMAction.WallExchange`: the
inter-wall link `Y` is Hermitian exactly when the update is symmetric under the wall-parity
exchange. `PMAction.InterWallDiagonal` and `LabelInsertion` split on whether it is. This module
settles it for the equal-class crossing within one orientation convention.

`Y` is the wall-`false`-to-wall-`true` block (`hop ⊗ Y`). An equal-class crossing at class `c` takes
the wall-`false` mode of class `c`, in generation `omitted false c = c + 1`, to the wall-`true` mode of
class `c`, in generation `omitted true c = c − 1`.
* `crossing_entry`: so its entry is at (wall-`true` generation, wall-`false` generation)
  `= (h + 1, h)` with `h = c + 1`: one direction around the generation cycle.
* `transpose_disjoint`: no crossing has its entry at a transposed position `(h, h + 1)`.
* `hermitian_only_if_zero`: a matrix supported on positions disjoint from their transposes is
  Hermitian only if it is zero.

So within one convention the crossing link is never Hermitian unless it vanishes: the wall-parity
exchange symmetry is broken by the vacuum's choice of convention (`GenerationWalls`'
`balanced_classification`), as chirality is. For `PMFlavor` this is the directional case of
`InterWallDiagonal`: `WallSeesaw` gives one Dirac pair per class, `δ²/|y_c|`, pairing generation `h`
on one wall with `h + 1` on the other; with a class-independent crossing (`DomainWall`'s hop is one
fixed matrix) those three are equal, so the hierarchy comes from the composite of `GenerationDiagonal`.

Strong CP: the older route `PMConstants.HermitianMass.thetaBar_eq_theta` assumes a Hermitian link,
which this excludes. The current route, `ThetaBarSelection`, gives `θ̄ = 0` for any invertible mass
(`Zm_eq`: the vacuum sees only `θ − arg det M`), so the non-Hermitian link does not affect it.
-/

namespace PMAction.GenerationParity
open GenerationWalls Matrix

/-- **A crossing at class `c` sits at (wall-`true` generation, wall-`false` generation)
`= (h + 1, h)` with `h = c + 1`.** -/
theorem crossing_entry : ∀ c : Fin 3, omitted true c = omitted false c + 1 := by decide

/-- **No crossing sits at a transposed position.** -/
theorem transpose_disjoint : ∀ c c' : Fin 3,
    (omitted true c, omitted false c) ≠ (omitted false c', omitted true c') := by decide

/-- **A matrix supported on positions disjoint from their transposes is Hermitian only if zero.** -/
theorem hermitian_only_if_zero {n : Type*} (S : n → n → Prop) (Y : Matrix n n ℂ)
    (hsupp : ∀ i j, ¬ S i j → Y i j = 0) (hdisj : ∀ i j, S i j → ¬ S j i)
    (hH : Y.IsHermitian) : Y = 0 := by
  ext i j
  by_cases h : S i j
  · have hji : Y j i = 0 := hsupp j i (hdisj i j h)
    have := congrFun (congrFun hH i) j
    rw [conjTranspose_apply] at this
    rw [← this, hji, star_zero]
    rfl
  · rw [hsupp i j h]; rfl

end PMAction.GenerationParity
