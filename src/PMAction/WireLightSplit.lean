import PMAction.ReferenceWallRotation

/-!
# The wire splits the light pair: a Fibonacci block

`ReferenceWallMass`: `M = D_R (δ_O + cyc κ_O)`. With `UndetunedWall`'s bookkeeping (rows carry
`(K, k, k)`, the shift carries `κ_O = (K, k, k)`: vector flip `K`, spinor flip `k`) the rows are

  `K (δ, 0, k)`,  `k (K, δ, 0)`,  `k (0, k, δ)`.

When `δ` and `k` are small against `K` (the regime where `δ_O` is a few spinor flips), the first two
rows carry the two larger masses through the block of columns `0, 2`:
`B = [[K δ, K k], [k K, 0]] = K · [[δ, k], [k, 0]]`, and the third row is smaller by a factor `k`.

* `block_char`: the eigenvalues `λ` of `[[δ, k], [k, 0]]` solve `λ² − δ λ − k² = 0`, so their product is
  `−k²` (`block_product`).
* `ratio_relation`: for the positive root, `λ/k − k/λ = δ/k`. With `m₀ = K λ₊`, `m₁ = K k²/λ₊`:
  `√(m₀/m₁) − √(m₁/m₀) = δ_O/k`. The ratio of the two larger masses is fixed by `δ_O/k` alone.
* `golden_point`: at `δ_O = k` the block is the Fibonacci matrix `[[1, 1], [1, 0]]` (times `k`), and
  `λ₊ = k φ`: masses `K k φ` and `K k/φ`.
* The third mass is `|det M|/(m₀ m₁) = |δ³ + K k²|/K` (`ReferenceWallRotation.det_M`), `≈ k²` when
  `δ³ ≪ K k²`.

**Numerical check (outside Lean).** With `k/K = α/2` the three predicted masses match the singular
values of `M` to `< 1%` for `δ_O/k ≤ 3` and to `3%` at `7`; with `k/K = 0.0385` (the rate reading of
the admittance ratio) only up to `δ_O/k ≈ 1`.

**Consequence.** In this regime the wire gives, parameter-free in the ratios,
`(m₂/m₁) · √(m₀/m₁) ≈ k/K`: the lightest-to-middle ratio times the square root of heavy-to-middle is
the spinor-to-vector flip ratio. Whether any protocol's masses are the wire's singular values directly
is PMElementaryParticles' question; this relation is what such a protocol would have to satisfy. The
mechanism: the vector carrier's entry at `(1, 0)` couples label `1` to the heavy label `0`; for
`δ_O ≫ k` the heavy state absorbs it and labels `1`, `2` end near-degenerate, for `δ_O ∼ k` it does not.
-/

namespace PMAction.WireLightSplit

/-- **Vieta for the block**: if `λ² − δλ − k² = 0` for both roots, their product is `−k²`. -/
theorem block_product (δ k l₁ l₂ : ℝ) (hne : l₁ ≠ l₂) (h₁ : l₁ ^ 2 - δ * l₁ - k ^ 2 = 0)
    (h₂ : l₂ ^ 2 - δ * l₂ - k ^ 2 = 0) : l₁ * l₂ = -k ^ 2 := by
  have hs : l₁ + l₂ = δ := by
    have : (l₁ - l₂) * (l₁ + l₂ - δ) = 0 := by linear_combination h₁ - h₂
    have h' : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr hne
    linarith [(mul_eq_zero.mp this).resolve_left h']
  have : l₁ * l₂ = l₁ * (δ - l₁) := by rw [← hs]; ring
  rw [this]; linear_combination -h₁

/-- **The eigenvalue equation of `[[δ, k], [k, 0]]`.** -/
theorem block_char (δ k l : ℝ) :
    (Matrix.det (!![δ - l, k; k, -l] : Matrix (Fin 2) (Fin 2) ℝ) = 0) ↔ l ^ 2 - δ * l - k ^ 2 = 0 := by
  rw [Matrix.det_fin_two_of]
  constructor <;> intro h <;> linear_combination h

/-- **The ratio relation**: `λ/k − k/λ = δ/k`. -/
theorem ratio_relation (δ k l : ℝ) (hk : k ≠ 0) (hl : l ≠ 0) (h : l ^ 2 - δ * l - k ^ 2 = 0) :
    l / k - k / l = δ / k := by
  rw [div_sub_div _ _ hk hl, div_eq_div_iff (mul_ne_zero hk hl) hk]
  linear_combination k * h

/-- **At `δ = k` the larger root is `k φ`.** -/
theorem golden_point (k : ℝ) :
    (k * ((1 + Real.sqrt 5) / 2)) ^ 2 - k * (k * ((1 + Real.sqrt 5) / 2)) - k ^ 2 = 0 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (k ^ 2 / 4) * h5

end PMAction.WireLightSplit
