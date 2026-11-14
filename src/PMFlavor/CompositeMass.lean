import PMFlavor.CyclicSeesaw

/-!
# Where the composite mass enters the two-wall Hamiltonian

`PMConstants.GenerationMass`: within one convention a generation-diagonal mass is a composite, an
equal-class crossing and a single-wall carrier of the generation's label class. `CyclicSeesaw`: the
crossing alone gives three equal seesaw masses. This module places the carrier in `WallSeesaw`.

* `effective_mass_general`: if the on-site chirality flips carry generation structure (`D₁` on wall
  1, `D₂` on wall 2, in place of `δ · 1`), the zero-energy Schur complement gives the light Dirac
  mass `M = D₂ Y⁻¹ D₁ᴴ`. `WallSeesaw.effective_mass` is the case `D₁ = D₂ = δ`.
* `inv_cyc`: the crossing link `cyc y` inverts to `cycInv y`, the reverse cyclic shift with entries
  `1 / y h`.
* `cyc_mul_cycInv`, `cycInv_mul_cyc`: a carrier with the crossing's own support `(h + 1, h)`,
  placed on either side of `Y⁻¹`, gives a diagonal matrix, entries `κ / y`. That support is the
  wall-`false` shift of `GenerationMass.composite_cross_then_shift` (`h → h + 1`).
* `composite_expansion`: with `D₂ = δ + cyc κ` and `D₁ᴴ = δ + cyc κ'`,
  `M = δ² Y⁻¹ + δ · diag(κ'/y) + δ · diag(κ/y) + diag(κ/y) · cyc κ'` (the last is
  `cyc κ · Y⁻¹ · cyc κ'`).
  The first and last terms are generation-changing (cyclic); the two middle terms are the composite,
  generation-diagonal and linear in the carrier amplitude.

So the composite is a correction to `δ`, not a separate direct term: item (2) of PMAction's "Mass
terms". The diagonal mass is linear in `κ`, so the generation with the largest carrier amplitude is
the heaviest. That agrees with the direction `MassInsertion` says the data choose.

**Premise (candidate).** The single-wall carrier acts as a chirality flip on its wall, in the slot of
`δβ`. A carrier that keeps chirality acts on the zero modes and does not give a mass this way.

**Test.** `M` is not generation-diagonal. With `|κ| ≫ |δ|` the masses are near `δ|κ_g|/|y|`, and the
cyclic `δ²/y` term mixes the generations at relative size `δ/κ`. If the carrier amplitudes are
derived, that mixing is a prediction for the CKM, not a parameter. If `|κ| ≲ |δ|` the masses are close
to equal, which the data exclude.
-/

noncomputable section
namespace PMFlavor.CompositeMass
open Matrix PMFlavor.CyclicSeesaw PMAction.WallSeesaw

section General
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- On-site chirality flips with generation structure: `D₁` joins `a ↔ b`, `D₂` joins `d ↔ c`. -/
def V2 (D₁ D₂ : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks D₁ 0 0 D₂

/-- **The light Dirac mass is `D₂ Y⁻¹ D₁ᴴ`.** -/
theorem effective_mass_general (Y D₁ D₂ : Matrix n n ℂ) :
    -(V2 D₁ D₂ * Ginv Y * (V2 D₁ D₂)ᴴ) =
      fromBlocks 0 (D₁ * (Yᴴ)⁻¹ * D₂ᴴ) (D₂ * Y⁻¹ * D₁ᴴ) (0 : Matrix n n ℂ) := by
  rw [V2, Ginv, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [fromBlocks_neg, Matrix.mul_assoc]

end General

/-- The reverse cyclic shift with entries `1 / y h` at `(h, h + 1)`. -/
def cycInv (y : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (y 0)⁻¹, 0; 0, 0, (y 1)⁻¹; (y 2)⁻¹, 0, 0]

theorem cycInv_mul (y : Fin 3 → ℂ) (hy : ∀ j, y j ≠ 0) : cycInv y * cyc y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycInv, cyc, Matrix.mul_apply, Fin.sum_univ_three, inv_mul_cancel₀ (hy _)]

/-- **The crossing link inverts to the reverse shift.** -/
theorem inv_cyc (y : Fin 3 → ℂ) (hy : ∀ j, y j ≠ 0) : (cyc y)⁻¹ = cycInv y :=
  inv_eq_left_inv (cycInv_mul y hy)

/-- **A carrier with the crossing's support, after `Y⁻¹`, is diagonal.** -/
theorem cyc_mul_cycInv (κ y : Fin 3 → ℂ) :
    cyc κ * cycInv y = diagonal ![κ 2 * (y 2)⁻¹, κ 0 * (y 0)⁻¹, κ 1 * (y 1)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycInv, cyc, Matrix.mul_apply, Fin.sum_univ_three]

/-- **A carrier with the crossing's support, before `Y⁻¹`, is diagonal.** -/
theorem cycInv_mul_cyc (y κ : Fin 3 → ℂ) :
    cycInv y * cyc κ = diagonal fun j => (y j)⁻¹ * κ j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycInv, cyc, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The light mass with carriers in the chirality-flip slots.** -/
theorem composite_expansion (y κ κ' : Fin 3 → ℂ) (δ : ℂ) (hy : ∀ j, y j ≠ 0) :
    (δ • (1 : Matrix (Fin 3) (Fin 3) ℂ) + cyc κ) * (cyc y)⁻¹ * (δ • 1 + cyc κ') =
      (δ * δ) • cycInv y + δ • diagonal (fun j => (y j)⁻¹ * κ' j)
        + (δ • diagonal ![κ 2 * (y 2)⁻¹, κ 0 * (y 0)⁻¹, κ 1 * (y 1)⁻¹]
          + diagonal ![κ 2 * (y 2)⁻¹, κ 0 * (y 0)⁻¹, κ 1 * (y 1)⁻¹] * cyc κ') := by
  rw [inv_cyc y hy]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    cyc_mul_cycInv, cycInv_mul_cyc]
  rw [smul_add, smul_smul]
  abel

end PMFlavor.CompositeMass
