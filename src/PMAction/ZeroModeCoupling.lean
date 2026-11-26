import PMAction.DomainWall

/-!
# The direct zero-mode coupling is the off-Wilson part of the inter-sector hop

`PMAction.LabelInsertion` closed the routes that get the charged masses by inverting a link
(`δ²Y⁻¹`, `D Y⁻¹ D`) and left a term joining the two chiral zero modes directly. This module finds
where such a term sits in the two-slice wall of `DomainWall`.

The inter-sector hop with Wilson parameter `r` is `−β(r + Γ)/2` (`DomainWall`: `−(iα₄ + rβ)/2` with
`Γ = iβα₄`, so `iα₄ = βΓ`). The zero modes are `Γ = +1` on wall 1 and `Γ = −1` on wall 2
(`DomainWall.zero_modes`).
* `hop_split`: `β(r + Γ) = ((r+1)/2)·β(1+Γ) + ((r−1)/2)·β(1−Γ)`.
* `wilson_kills`: the `β(1+Γ)` part annihilates wall 2's zero mode (the content of
  `DomainWall.zero_modes`). At the Wilson point `r = 1` the hop is this part alone, so it has no
  matrix element between the zero modes: an equal-class crossing at `r = 1` enters the light mass
  only through the gapped components (the `WallSeesaw` route), not directly.
* `off_wilson_joins`, `off_wilson_lands_plus`, `off_wilson_nonzero`: the `β(1−Γ)` part takes wall 2's
  zero mode `x` to `2βx`, a nonzero `Γ = +1` vector, the zero-mode slot of wall 1.
* `zero_mode_element`: on wall 2's zero mode the full hop, `β(r x + Γ x)`, gives `(r − 1)·βx`. **The direct
  zero-mode coupling is proportional to `r − 1`**: zero at the Wilson point, the residual mass of
  the two-slice wall.

For flavour: the direct light-mode term needs `r ≠ 1` (or another off-Wilson source) as a common
factor; the class dependence of the masses is the node passage, not a class-dependent `r`
(`PMFlavor.TickPlacement`). The equal-class crossing, at `r = 1`, stays out of the direct mass; its
seesaw contribution (size `δ²/|Y|`) must be small against the direct term for the masses to stay
generation-diagonal.
-/

namespace PMAction.ZeroModeCoupling
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Wilson hop splits into an on-Wilson and an off-Wilson part.** -/
theorem hop_split (β Γ : Matrix n n ℂ) (r : ℂ) :
    β * (r • (1 : Matrix n n ℂ) + Γ) =
      ((r + 1) / 2) • (β * (1 + Γ)) + ((r - 1) / 2) • (β * (1 - Γ)) := by
  simp only [mul_add, mul_sub, mul_one, Matrix.mul_smul]
  module

/-- **The on-Wilson part annihilates wall 2's zero mode.** -/
theorem wilson_kills (β Γ : Matrix n n ℂ) (x : n → ℂ) (hx : Γ *ᵥ x = -x) :
    (β * (1 + Γ)) *ᵥ x = 0 := by
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hx, add_neg_cancel,
    Matrix.mulVec_zero]

/-- **The off-Wilson part takes wall 2's zero mode to `2βx`.** -/
theorem off_wilson_joins (β Γ : Matrix n n ℂ) (x : n → ℂ) (hx : Γ *ᵥ x = -x) :
    (β * (1 - Γ)) *ᵥ x = (2 : ℂ) • (β *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_neg_eq_add,
    ← two_smul ℂ x, Matrix.mulVec_smul]

omit [DecidableEq n] in
/-- `βx` has chirality `+1`: it lies in wall 1's zero-mode slot. -/
theorem off_wilson_lands_plus (β Γ : Matrix n n ℂ) (hΓβ : Γ * β = -(β * Γ)) (x : n → ℂ)
    (hx : Γ *ᵥ x = -x) : Γ *ᵥ (β *ᵥ x) = β *ᵥ x := by
  rw [Matrix.mulVec_mulVec, hΓβ, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hx,
    Matrix.mulVec_neg, neg_neg]

/-- `βx ≠ 0` for `x ≠ 0`, since `β² = 1`. -/
theorem off_wilson_nonzero (β : Matrix n n ℂ) (hβ : β * β = 1) (x : n → ℂ) (hx0 : x ≠ 0) :
    β *ᵥ x ≠ 0 := by
  intro h
  apply hx0
  have h2 := congrArg (fun z => β *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, hβ] using h2

omit [DecidableEq n] in
/-- **The direct zero-mode coupling is `(r − 1)·βx`.** The hop `β(r + Γ)` applied to wall 2's zero
mode is `β(r x + Γ x)`, and `Γ x = −x`. -/
theorem zero_mode_element (β Γ : Matrix n n ℂ) (r : ℂ) (x : n → ℂ) (hx : Γ *ᵥ x = -x) :
    β *ᵥ (r • x + Γ *ᵥ x) = (r - 1) • (β *ᵥ x) := by
  rw [hx, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg]
  module

end PMAction.ZeroModeCoupling
