import PMAction.ChiralityConvention

/-!
# The reference wall carries no on-site detuning

`DetuningMass` adds the on-site detuning `δβ` on both sectors equally; nothing fixes the value per
wall. `ChiralityConvention.physicalBackground` places Paper II's stationary reference background on
the second wall, components `(0, 0, a, b)`. Allow a separate detuning on each wall:
`Hw δ₁ δ₂ = [[δ₁β, hop], [back, δ₂β]]` at `k = 0` (`Hw_equal`: `Hw δ δ = hamiltonian 0 δ`).

* `second_wall_action`: `Hw δ₁ δ₂` sends `(0, 0, a, b)` on the second wall to `δ₂ (a, b, 0, 0)` on
  the same wall. The hops do not see it (`hop` kills the `Γ = −1` components) and `δ₁` does not
  reach it.
* `stationary_iff`: a nonzero second-wall background is a zero mode exactly when `δ₂ = 0`. The
  first wall's detuning is unconstrained.

**Reading.** If the reference persists as a stationary zero mode of the same update the flavour
fermions see (Paper II's stationarity, the premise `ChiralityConvention` already uses), the on-site
chirality flip vanishes on the reference's wall and lives only on the other one. That is the
maximal asymmetry `δ_R = 0` that `PMFlavor.LightSplit.near_maximal` requires, from a structural
source, not a perturbative one. Consequences in `PMFlavor.LightSplit` (`composite_expansion2` with
one `δ` zero): the seesaw term `δ_F δ_T Y⁻¹` vanishes, and every generation's composite mass uses
its label-class carrier on the reference's wall.
-/

noncomputable section
namespace PMAction.ReferenceDetuning
open Matrix ConcreteFermion

/-- The `k = 0` two-wall Hamiltonian with detuning `δ₁` on the first wall, `δ₂` on the second. -/
def Hw (δ₁ δ₂ : ℝ) : Matrix Sites Sites ℂ :=
  fromBlocks (δ₁ • beta) (DomainWallSpectrum.hop beta gamma) (DomainWallSpectrum.back beta gamma)
    (δ₂ • beta)

/-- **Equal detunings give the library's Hamiltonian at `k = 0`.** -/
theorem Hw_equal (δ : ℝ) : Hw δ δ = hamiltonian 0 δ := by
  simp [Hw, hamiltonian, DomainWallSpectrum.H, DomainWallSpectrum.momentum]

/-- **Action on a second-wall `Γ = −1` state.** -/
theorem second_wall_action (δ₁ δ₂ : ℝ) (a b : ℂ) :
    Hw δ₁ δ₂ *ᵥ Sum.elim (fun _ => 0) ![0, 0, a, b] =
      Sum.elim (fun _ => 0) ![(δ₂ : ℂ) * a, (δ₂ : ℂ) * b, 0, 0] := by
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [Hw, beta, gamma, DomainWallSpectrum.hop, DomainWallSpectrum.back,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, fromBlocks, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Fin.sum_univ_four, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      Sum.elim]

/-- **The second-wall background is stationary exactly when its wall has no detuning.** -/
theorem stationary_iff (δ₁ δ₂ : ℝ) (a b : ℂ) (hab : a ≠ 0 ∨ b ≠ 0) :
    Hw δ₁ δ₂ *ᵥ Sum.elim (fun _ => 0) ![0, 0, a, b] = 0 ↔ δ₂ = 0 := by
  rw [second_wall_action]
  constructor
  · intro h
    have h0 : (δ₂ : ℂ) * a = 0 := by simpa using congrFun h (Sum.inr 0)
    have h1 : (δ₂ : ℂ) * b = 0 := by simpa using congrFun h (Sum.inr 1)
    rcases hab with ha | hb
    · exact_mod_cast (mul_eq_zero.mp h0).resolve_right ha
    · exact_mod_cast (mul_eq_zero.mp h1).resolve_right hb
  · rintro rfl
    ext x
    rcases x with i | i <;> fin_cases i <;> simp

/-- **The physical reference background has this form.** -/
theorem physical_form (r : Fin 2 → ℂ) :
    ChiralityConvention.physicalBackground r = Sum.elim (fun _ => 0)
      ![0, 0, (Real.sqrt 2 : ℂ) * r 0, (Real.sqrt 2 : ℂ) * r 1] :=
  ChiralityConvention.physicalBackground_apply r

end PMAction.ReferenceDetuning
