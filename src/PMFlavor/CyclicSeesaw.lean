import PMConstants.GenerationParity
import PMAction.WallSeesaw

/-!
# The seesaw on the one-directional crossing link

Step 6 of the generation sector (`PMAction/REVIEW-AND-NEXT.md`): what steps 1 to 5 give the flavour
sector. Within one orientation convention the equal-class crossing puts the inter-wall link `Y`
(wall-`false` generation to wall-`true` generation) only at the positions `(h + 1, h)`
(`PMConstants.GenerationParity.crossing_entry`). So `Y` is a weighted cyclic shift `cyc y`, one
crossing amplitude `y h` per class.

* `cyc_support`: `cyc y` vanishes off `(h + 1, h)`, the support `GenerationParity` allows.
* `gram_cyc`: `Yᴴ Y` is diagonal with entries `|y h|²`. With `WallSeesaw.seesaw`
  (`seesaw_cyc`), the light Dirac masses are `δ² / |y h|`, one per class, and each pairs the
  generation `h` of one wall with `h + 1` of the other. The weak current acts on one wall
  (`PMConstants.GenerationWeak`), so it sees only one of the two labels.
* `gram_equal`: a class-independent crossing (`DomainWall`'s one hop) gives `Yᴴ Y = |a|² · 1`, so
  the three seesaw masses are equal. The seesaw does not carry the hierarchy; the generation-diagonal
  composite of `PMConstants.GenerationMass` must.
* `det_cyc`: `det Y = y 0 · y 1 · y 2`, with sign `+` (the 3-cycle is even).
  `det_cyc_real`, `light_det_real`: for real amplitudes `det Y` and `det M` are real, so
  `arg det M ∈ {0, π}`. This bears only on the older Hermitian-mass route to `θ̄ = 0`
  (`PMConstants.HermitianMass`), and reality alone still allows `π` there. The current route,
  `PMConstants.ThetaBarSelection`, gives `θ̄ = 0` for any invertible mass, so neither this nor the
  phase of the composite diagonal term is a strong-CP prerequisite; the composite phase is a flavour
  question.

Falsification: if the composite diagonal term is shown to vanish or to be class-independent, then
this sector predicts three degenerate charged masses per sector, which the data exclude.
-/

noncomputable section
namespace PMFlavor.CyclicSeesaw
open Matrix PMAction.WallSeesaw

/-- The weighted cyclic shift: crossing amplitude `y h` at `(h + 1, h)`. -/
def cyc (y : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, y 2; y 0, 0, 0; 0, y 1, 0]

/-- **`cyc y` lives on the crossing support `(h + 1, h)`.** -/
theorem cyc_support (y : Fin 3 → ℂ) : ∀ i j : Fin 3, i ≠ j + 1 → cyc y i j = 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | exact (h (by decide)).elim | rfl

/-- **`Yᴴ Y` is diagonal**, entries `|y h|²`. -/
theorem gram_cyc (y : Fin 3 → ℂ) :
    (cyc y)ᴴ * cyc y = diagonal fun j => star (y j) * y j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]

/-- **Seesaw on the crossing link**: `M Mᴴ = δ⁴ · diag(|y h|²)⁻¹`. -/
theorem seesaw_cyc (y : Fin 3 → ℂ) (δ : ℝ) :
    light δ (cyc y) * (light δ (cyc y))ᴴ =
      (δ ^ 4 : ℝ) • (diagonal fun j => star (y j) * y j)⁻¹ := by
  rw [seesaw, gram_cyc]

/-- **A class-independent crossing gives equal seesaw masses**: `Yᴴ Y = |a|² · 1`. -/
theorem gram_equal (a : ℂ) : (cyc fun _ => a)ᴴ * cyc (fun _ => a) = (star a * a) • 1 := by
  rw [gram_cyc, smul_one_eq_diagonal]

/-- **`det Y = y 0 · y 1 · y 2`** (the 3-cycle is even). -/
theorem det_cyc (y : Fin 3 → ℂ) : (cyc y).det = y 0 * y 1 * y 2 := by
  rw [Matrix.det_fin_three]
  simp [cyc]
  ring

/-- **Real amplitudes give a real determinant.** -/
theorem det_cyc_real (y : Fin 3 → ℝ) :
    (cyc fun j => (y j : ℂ)).det = ((y 0 * y 1 * y 2 : ℝ) : ℂ) := by
  rw [det_cyc]; push_cast; ring

/-- **Real amplitudes give a real `det M`**: `det M = δ⁶ / (y 0 y 1 y 2)`. -/
theorem light_det_real (y : Fin 3 → ℝ) (δ : ℝ) :
    (light δ (cyc fun j => (y j : ℂ))).det = (((δ ^ 2) ^ 3 / (y 0 * y 1 * y 2) : ℝ) : ℂ) := by
  rw [light_det, det_cyc_real]
  simp only [Fintype.card_fin]
  push_cast
  ring

end PMFlavor.CyclicSeesaw
