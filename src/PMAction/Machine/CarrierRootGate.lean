import PMAction.Machine.CarrierWeyl
import PMAction.Machine.CoherentPreparation

/-!
# The comparison gate's coherent step from one root reflection

`CoherentPreparation` makes the two-support state from a quarter period of evolution under any
Hermitian involution. The carriers' own simple root reflections (`CarrierWeyl.simple`, certified
E8 reflections, `simple_is_root`) are such involutions:

* `simple_symm`, `simple_sq`: each simple reflection is its own inverse.
* `root_hermitian`, `root_involution`: its permutation matrix `R` is Hermitian with `R² = 1`.
* `root_gate_unitary`: so the quarter-period gate `(1 + iR)/√2` of one root reflection is unitary,
  and by `CoherentPreparation.quarter_gate_prepares` it takes a carrier to the coherent pair of that
  carrier and its reflection.

So the comparison gate's coherent step is a single root word of length one, run for a quarter
period. The remaining gate content is the controlled transport, whose root words are the
directional hops (`AxisHop`).
-/

noncomputable section
namespace PMAction.CarrierRootGate
open Matrix CarrierEvents CarrierWeyl CoherentPreparation

/-- A simple reflection is its own inverse. -/
theorem simple_symm (c : Fin 3) (j : Fin 4) : (simple c j).symm = simple c j :=
  Equiv.ext fun _ => rfl

theorem simple_sq (c : Fin 3) (j : Fin 4) : simple c j * simple c j = 1 :=
  Equiv.ext fun v => Subtype.ext (simple_twice j v.1)

/-- **A root reflection's matrix is Hermitian.** -/
theorem root_hermitian (c : Fin 3) (j : Fin 4) :
    ((simple c j).permMatrix ℂ)ᴴ = (simple c j).permMatrix ℂ := by
  rw [conjTranspose_permMatrix, Equiv.Perm.inv_def, simple_symm]

/-- **A root reflection's matrix squares to the identity.** -/
theorem root_involution (c : Fin 3) (j : Fin 4) :
    (simple c j).permMatrix ℂ * (simple c j).permMatrix ℂ = 1 := by
  rw [← permMatrix_mul, simple_sq, permMatrix_one]

/-- **The quarter-period gate of one root reflection is unitary.** -/
theorem root_gate_unitary (c : Fin 3) (j : Fin 4) :
    quarterGate ((simple c j).permMatrix ℂ) * (quarterGate ((simple c j).permMatrix ℂ))ᴴ = 1 :=
  quarter_gate_unitary _ (root_hermitian c j) (root_involution c j)

end PMAction.CarrierRootGate
