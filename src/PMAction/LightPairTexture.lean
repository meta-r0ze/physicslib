import Mathlib.Tactic

/-!
# The vector carrier on the light pair gives `tan θ₁₂ = √(m₁/m₂)` exactly

**Bookkeeping.** `PMAction.GenerationCurrent`: on wall `true` the change `g → g + 1` uses a carrier of
class `g − 1`; `PMConstants.GenerationWeak.weak_edge_true`, `weak_edge_false`: the vector-class carrier
joins generations `1` and `2`, the two light ones, on either wall. So in the other wall's carrier
matrix `cyc κ_O` the entry `(h + 1, h)` carries class `h − 1`: `(1, 0)` class `2`, `(2, 1)` class `0`
(vector, `K`), `(0, 2)` class `1`. `UndetunedWall` assigned class `h` to `(h + 1, h)` (vector at `(1, 0)`,
joining the heavy label to a light one), which does not match `GenerationCurrent`. With the matching
assignment, rows `(K, k, k)` (`composite_carrier_is_label`) and the shift `(k, K, k)`.

**The light block.** With `K = 1` and `k ≪ δ ≪ 1` the light labels' rows, restricted to the light
columns, are `k · [[δ, 0], [1, δ]]` up to corrections of order `k`. For `B = [[δ, 0], [1, δ]]`:
* `gram`: `B Bᵀ = [[δ², δ], [δ, 1 + δ²]]`.
* `light_vectors`: with `δ (1 − t²) = t`, `t² · B Bᵀ (t, 1) = δ² (t, 1)` and `B Bᵀ (1, −t) = (δ t)² (1, −t)`.
  So the two singular values are `δ/t` and `δ t`, their ratio is `t²`, and the heavier light state
  is `(t, 1)`: its admixture of the lighter label is `tan θ = t`.

So `tan θ₁₂ = √(m_lighter/m_heavier)` exactly at this order: the Gatto–Sartori–Tonin relation, from
the vector carrier sitting on the light pair, with no parameter beyond `δ`. Data: down
`√(m_d/m_s) = 0.2239` (FLAG `m_s/m_d = 19.95`), up `√(m_u/m_c) ≈ 0.045`; with the two at a relative
phase near `90°`, `|V_us| ≈ 0.223` against `0.2243`. Numerically on the full wire (outside Lean), fixing
`δ_O` by `m_d/m_s` with `k/K = α/2` gives `sin θ₁₂ = 0.218` (`tan θ₁₂ = 0.224`) and `m_s/m_b = 0.0163` against
`0.0185` (FLAG `m_b/m_s ≈ 54`). Open: the same vector carrier also makes PMFlavor's in-cycle label
change (`EventTransfer`, `κ₀ = π/14 = 0.2244`); counting it both in `J` and in `U_d` would double it.
-/

namespace PMAction.LightPairTexture
open Matrix

/-- The light block. -/
def B (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![δ, 0; 1, δ]

/-- **Its Gram matrix.** -/
theorem gram (δ : ℝ) : B δ * (B δ)ᵀ = !![δ ^ 2, δ; δ, 1 + δ ^ 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

/-- **The two light states and their masses.** With `δ (1 − t²) = t`, `(t, 1)` has squared singular
value `(δ/t)²` (stated as `t² · G (t, 1) = δ² · (t, 1)`) and `(1, −t)` has `(δ t)²`. -/
theorem light_vectors (δ t : ℝ) (h : δ * (1 - t ^ 2) = t) :
    t ^ 2 • ((!![δ ^ 2, δ; δ, 1 + δ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![t, 1]) = δ ^ 2 • ![t, 1] ∧
    (!![δ ^ 2, δ; δ, 1 + δ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, -t] = (δ * t) ^ 2 • ![1, -t] := by
  constructor
  · ext i; fin_cases i
    · simp
      linear_combination (-δ * t) * h
    · simp
      linear_combination (-(t + δ)) * h
  · ext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination δ * h
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (1 - t * δ) * h

/-- **Mass ratio is `t²`, mixing is `tan θ = t`**: `(δ t)/(δ/t) = t²`. -/
theorem ratio (δ t : ℝ) (ht : t ≠ 0) (hδ : δ ≠ 0) : (δ * t) / (δ / t) = t ^ 2 := by
  field_simp

end PMAction.LightPairTexture
