import PMAction.ReferenceWallRotation
import PMAction.GenerationCurrent
import PMAction.UndetunedWall

/-!
# The detuned wire operator with carriers placed by glue arithmetic

`ReferenceWallFactorization`: the light-sector operator is `M = D_R (δ_O + cyc κ_O)`, `D_R` the reference wall's carriers
by label (row `g` carries `κ_R(e g)`), and `cyc c` puts `c h` at `(h + 1, h)` (`CyclicSeesaw.cyc`). The
right factor acts on the other wall's single-wall modes. On those modes (`GenerationWalls`: a
wall-`true` mode of class `c` belongs to generation `c − 1`) the move joining generations `h` and
`h + 1` changes the class by `e (h + 1) + e (h + 2) = e h` (`single_wall_class`). There is no other
choice: the class at `(h + 1, h)` is `h`. This is the assignment of `LightSplit.composite_expansion2`
and `GenerationDiagonal.composite_shift_then_cross`.

`GenerationCurrent.edge_carrier`'s class `e (h − 1)` is the carrier of a two-wall label change, which
also needs a glue move `e (h + 1)` on both walls. A one-wall factor cannot contain that move, so it
does not place the carriers in the single-wall operator. (A 2026-11 "bookkeeping correction" used it; it mixed the two
state spaces of `GenerationSector` and is withdrawn, PMAction OVERVIEW.)

* `shift κ_O`: the other wall's carrier entries, `shift κ_O h = κ_O h`, class `h` at `(h + 1, h)`.
* `shift_entry`, `single_wall_class`.
* `vector_on_heavy_edge`: the vector class `0` sits at `(1, 0)`, joining the heavy label `0` to label `1`.
* `detunedWireOperator δ κ_R κ_O = diag κ_R · (δ + cyc (shift κ_O))`.
* `undetuned`: at `δ = 0` with the swap × exchange symmetry (`κ_O = (K, k_c, k_s)`): entries
  `(k_s K, k_c², K k_s)`, singular values `(kK, k², kK)` (`UndetunedWall.undetuned_operator`).
* `det_detunedWireOperator`: `det = κ_R 0 κ_R 1 κ_R 2 (δ³ + κ_O 0 κ_O 1 κ_O 2)`.
-/

noncomputable section
namespace PMAction.DetunedWire
open Matrix PMAction.CyclicSeesaw PMAction.ReferenceWallRotation

/-- The other wall's carrier entries by edge: the move `h → h + 1` has class `h`. -/
def shift (κO : Fin 3 → ℂ) : Fin 3 → ℂ := fun h => κO h

/-- The light-sector wire operator `diag κ_R · (δ + cyc (shift κ_O))`. -/
def detunedWireOperator (δ : ℂ) (κR κO : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := diagonal κR * X δ (shift κO)

/-- **Single-wall class arithmetic**: on wall `true` the modes of generations `h` and `h + 1` have
classes `e (h + 1)` and `e (h + 2)`; the move between them changes the class by `e h`. -/
theorem single_wall_class (e : Fin 3 → GenerationSector.Glue) (he : GenerationOrientation.Good e)
    (h : Fin 3) : e (h + 1) + e (h + 1 + 1) = e h := by
  revert e h; decide +kernel

/-- **The entry at `(h + 1, h)` is the class-`h` carrier.** -/
theorem shift_entry (κO : Fin 3 → ℂ) (h : Fin 3) : cyc (shift κO) (h + 1) h = κO h := by
  fin_cases h <;> rfl

/-- **The vector carrier joins the heavy label `0` to label `1`.** -/
theorem vector_on_heavy_edge (κO : Fin 3 → ℂ) : cyc (shift κO) 1 0 = κO 0 := rfl

/-- **Undetuned, with the swap × exchange symmetry**: `UndetunedWall.undetuned_operator`. -/
theorem undetuned (K ks kc : ℂ) :
    detunedWireOperator 0 ![K, ks, kc] ![K, kc, ks] = cyc ![ks * K, kc * kc, K * ks] := by
  simp only [detunedWireOperator, X, zero_smul, zero_add]
  exact UndetunedWall.undetuned_operator K ks kc

/-- **The determinant.** -/
theorem det_detunedWireOperator (δ : ℂ) (κR κO : Fin 3 → ℂ) :
    (detunedWireOperator δ κR κO).det = κR 0 * κR 1 * κR 2 * (δ ^ 3 + κO 0 * κO 1 * κO 2) := by
  rw [detunedWireOperator, det_M]
  rfl

end PMAction.DetunedWire
