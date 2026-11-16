import PMAction.ConcreteFermion
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Colour cannot act on the carrier axes: the Dirac structure has only scalar commutant

`CarrierVacuumSector`, `NativeDetuning`: the wall's Dirac matrices `β`, `αⱼ` act on the four carrier
coordinates (axes `0…3`). Premise (Conservation): colour persists under the wall's own terms, so
its action commutes with the Dirac structure, the kinetic `αⱼ` and the mass/flip `β`. Here the Dirac generators have only scalar
commutant on the four axes (`commutant_scalar`): any operator on the axes that commutes with `β` and
all `αⱼ` is a multiple of the identity. So no nontrivial colour action lives on the axes
(`colour_not_on_axes`); colour must be a separate register, a tensor factor on which the Dirac
structure acts trivially. This settles `NativeDetuning.colour_invariant_flip_zero` and
`PMConstants.ColourWallCrossing.no_faithful_joint_encoding` from the other side: the axis
identification of colour is excluded, not repaired. Readings that used colour as carrier axes under
`β` (`NativeDetuning`'s crossing fraction `1/3`, PMElementaryParticles `BetaReference`, since removed) need to be
re-derived with colour as a separate factor.

With colour a separate factor, the flavour and wall operators act as `A ⊗ 1` and colour as `1 ⊗ C`:
* `factor_commutes`: they commute for every `A` and `C`, so every crossing and flip is
  colour-equivariant and its weights are constant on colour orbits
  (`PMConstants.ColourWallCrossing.weighted_equivariant_iff`);
* `readout_colour_free`: a flavour readout `⟨ψ ⊗ χ, (A ⊗ 1)(ψ ⊗ χ)⟩` is `⟨ψ, Aψ⟩ ⟨χ, χ⟩`: it does
  not depend on the colour state, so a colour average is the readout itself.
-/

namespace PMAction.ColourRegister
open Matrix ConcreteFermion
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- **The Dirac generators have only scalar commutant on the carrier axes.** -/
theorem commutant_scalar (X : Spin) (hb : X * beta = beta * X)
    (ha : ∀ j, X * alpha j = alpha j * X) : X = X 0 0 • (1 : Spin) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (1/2) * congrFun (congrFun (ha 0) 0) 0 + (-Complex.I/2) * congrFun (congrFun (ha 1) 0) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (ha 2) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (ha 0) 0) 2 + (Complex.I/2) * congrFun (congrFun (ha 1) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (ha 0) 0) 0 + (-Complex.I/2) * congrFun (congrFun (ha 1) 0) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (ha 0) 0) 1
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1/2) * congrFun (congrFun (ha 0) 0) 2 + (-Complex.I/2) * congrFun (congrFun (ha 1) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (ha 0) 0) 3 + (1/2) * congrFun (congrFun (ha 2) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 0) 0 + (-1/2) * congrFun (congrFun (ha 2) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 0) 1 + (-1/2) * congrFun (congrFun (ha 0) 0) 2 + (Complex.I/2) * congrFun (congrFun (ha 1) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 0) 3 + (1/2) * congrFun (congrFun (ha 0) 0) 0 + (-Complex.I/2) * congrFun (congrFun (ha 1) 0) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 1) 0 + (-1/2) * congrFun (congrFun (ha 0) 0) 2 + (-Complex.I/2) * congrFun (congrFun (ha 1) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 1) 1 + (-1) * congrFun (congrFun (ha 0) 0) 3 + (1/2) * congrFun (congrFun (ha 2) 0) 2
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 1) 2 + (-1/2) * congrFun (congrFun (ha 0) 0) 0 + (-Complex.I/2) * congrFun (congrFun (ha 1) 0) 0
  · linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_four, beta, alpha, Matrix.smul_apply, Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)) (-1) * congrFun (congrFun (hb) 1) 3 + (-1) * congrFun (congrFun (ha 0) 0) 1

/-- **No nontrivial colour action on the axes**: an operator commuting with the Dirac structure that
is not scalar does not exist. -/
theorem colour_not_on_axes (X : Spin) (hb : X * beta = beta * X)
    (ha : ∀ j, X * alpha j = alpha j * X) (hX : ∀ c : ℂ, X ≠ c • 1) : False :=
  hX _ (commutant_scalar X hb ha)

open scoped Kronecker

/-- Flavour/wall operators and colour actions on separate factors commute. -/
theorem factor_commutes {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (C : Matrix n n ℂ) :
    (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ C) =
      ((1 : Matrix m m ℂ) ⊗ₖ C) * (A ⊗ₖ (1 : Matrix n n ℂ)) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]
  simp

/-- A flavour readout does not see the colour state. -/
theorem readout_colour_free {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (ψ : m → ℂ) (χ : n → ℂ) :
    star (fun p : m × n => ψ p.1 * χ p.2) ⬝ᵥ
        ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ fun p : m × n => ψ p.1 * χ p.2) =
      (star ψ ⬝ᵥ (A *ᵥ ψ)) * (star χ ⬝ᵥ χ) := by
  simp only [dotProduct, mulVec, kroneckerMap_apply, Fintype.sum_prod_type, Pi.star_apply,
    one_apply, star_mul']
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ x : n, (∑ x_1, ∑ x_2, (if x = x_2 then A i x_1 else 0) * (ψ x_1 * χ x_2)) =
      (∑ x_1, A i x_1 * ψ x_1) * χ x := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x_1 _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  simp only [h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end PMAction.ColourRegister
