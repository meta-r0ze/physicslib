import PMAction.TorusWilson

/-!
# The certificate's link phases carry the stated constant flux

`tools/unit_transfer_certificate.py`'s `phases(L, n₁₂, n₃₄)` gives each link `(μ, x)` a phase
`f_μ(x)` (the link value is `e^{2πi f}`): in each flux plane `(a, b, n)` = `(0, 1, n₁₂)`,
`(2, 3, n₃₄)`, the `b`-link gets `n x_a / L²`, and on the wrapping slice `x_a = L − 1` the `a`-link
gets `−n x_b / L`. `phase` is that formula, over `ℚ`.

* `plaq`: the phase around the plaquette at `x` in the `(a, b)` plane,
  `f_a(x) + f_b(x + â) − f_a(x + b̂) − f_b(x)`.
* `plaquette_flux`: at `L = 3`, `(n₁₂, n₃₄) = (1, −1)` (the unit history of the certificate), every
  plaquette in the `(0, 1)` plane carries `1/9`, every one in the `(2, 3)` plane `−1/9`, and every
  other plaquette `0`, each modulo an integer. So the field is constant, with total flux `1` and
  `−1` through the two planes and topological charge `n₁₂ n₃₄ = −1`.
* `plaquette_flux_trivial`: with `(0, 0)` every plaquette is an integer (zero field).

With `PMAction.TorusWilson` (the spin structure), the rest of the correspondence (that the script
assembles `wilsonH` with these links, in any site order) is the code review recorded in
`PMConstants.UnitTransferWitness`.
-/

namespace PMAction.TorusFlux

/-- The script's link phase `f_μ(x)` (in units of `2π`). -/
def phase (L : ℕ) (n₁₂ n₃₄ : ℤ) (μ : Fin 4) (x : Fin 4 → ℕ) : ℚ :=
  (if μ = 1 then (n₁₂ * x 0 : ℚ) / L ^ 2 else 0) +
  (if μ = 0 ∧ x 0 = L - 1 then -(n₁₂ * x 1 : ℚ) / L else 0) +
  (if μ = 3 then (n₃₄ * x 2 : ℚ) / L ^ 2 else 0) +
  (if μ = 2 ∧ x 2 = L - 1 then -(n₃₄ * x 3 : ℚ) / L else 0)

/-- Step one site along `μ` on the `L`-torus (coordinates in `{0, …, L − 1}`). -/
def step (L : ℕ) (x : Fin 4 → ℕ) (μ : Fin 4) : Fin 4 → ℕ :=
  Function.update x μ ((x μ + 1) % L)

/-- The phase around the plaquette at `x` in the `(a, b)` plane. -/
def plaq (L : ℕ) (n₁₂ n₃₄ : ℤ) (a b : Fin 4) (x : Fin 4 → ℕ) : ℚ :=
  phase L n₁₂ n₃₄ a x + phase L n₁₂ n₃₄ b (step L x a) -
    phase L n₁₂ n₃₄ a (step L x b) - phase L n₁₂ n₃₄ b x

/-- The stated flux per plaquette in the `(a, b)` plane. -/
def flux (L : ℕ) (n₁₂ n₃₄ : ℤ) (a b : Fin 4) : ℚ :=
  if a = 0 ∧ b = 1 then (n₁₂ : ℚ) / L ^ 2 else if a = 2 ∧ b = 3 then (n₃₄ : ℚ) / L ^ 2 else 0

/-- **The unit history's links carry the constant flux `(1/9, −1/9)` per plaquette.** -/
theorem plaquette_flux : ∀ x₀ x₁ x₂ x₃ : Fin 3, ∀ a b : Fin 4, a < b →
    (plaq 3 1 (-1) a b ![(x₀ : ℕ), x₁, x₂, x₃] - flux 3 1 (-1) a b).den = 1 := by
  decide +kernel

/-- **The trivial history's links carry no flux.** -/
theorem plaquette_flux_trivial : ∀ x₀ x₁ x₂ x₃ : Fin 3, ∀ a b : Fin 4, a < b →
    (plaq 3 0 0 a b ![(x₀ : ℕ), x₁, x₂, x₃]).den = 1 := by
  decide +kernel

end PMAction.TorusFlux
