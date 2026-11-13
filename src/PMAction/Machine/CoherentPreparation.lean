import PMAction.Machine.PrimitiveRecordBoundary

/-!
# The admitted coherent evolution prepares the two-support state

`PrimitiveRecordBoundary.cannot_prepare`: no basis-preserving gate (permutations and diagonal
phases) takes a basis seed to the coherent state `(|a⟩ + i|b⟩)/√2` the comparison gate needs.
Coherent Hermitian evolution is not basis-preserving, and it is admitted
(`PMAction.Admission`; `NativePacketUpdate.native_conserving`, `native_local`).

For a Hermitian involution `H` (`H² = 1`), such as a root-response operator
(`NativeRootGenerators.root_square`, `physical_hermitian`) or a directional hop
(`Admission.direction_admitted` uses `cos τ + i sin τ N`), the evolution
`exp(iτH) = cos τ + i sin τ H` at `τ = π/4` is `(1 + iH)/√2`.

* `quarter_gate_unitary`: `(1 + iH)/√2` is unitary.
* `quarter_gate_prepares`: if `H` sends `|a⟩` to `|b⟩`, it sends `|a⟩` to `(|a⟩ + i|b⟩)/√2`,
  exactly `PrimitiveRecordBoundary.quarterState a b`.

So the coherent resource is supplied by one quarter-period of admitted evolution, priced like
any factor (`ClockLedger`). What `cannot_prepare` excludes is only the basis-preserving library.
-/

noncomputable section
namespace PMAction.CoherentPreparation
open Matrix PrimitiveRecordBoundary
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quarter-period gate `(1 + iH)/√2 = exp(iπH/4)` for an involution `H`. -/
def quarterGate (H : Matrix n n ℂ) : Matrix n n ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 + Complex.I • H)

lemma half_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  have h : (1 / Real.sqrt 2 * (1 / Real.sqrt 2) : ℝ) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [← Complex.ofReal_mul, h]; push_cast; ring

/-- **The quarter-period gate is unitary.** -/
theorem quarter_gate_unitary (H : Matrix n n ℂ) (hH : Hᴴ = H) (hsq : H * H = 1) :
    quarterGate H * (quarterGate H)ᴴ = 1 := by
  have hct : (quarterGate H)ᴴ = ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 - Complex.I • H) := by
    unfold quarterGate
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_one, conjTranspose_smul, hH]
    simp [Complex.conj_ofReal, sub_eq_add_neg, neg_smul]
  have hprod : (1 + Complex.I • H) * (1 - Complex.I • H) = (2 : ℂ) • (1 : Matrix n n ℂ) := by
    simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, hsq, Complex.I_mul_I]
    module
  rw [hct]
  unfold quarterGate
  rw [smul_mul_smul_comm, hprod, smul_smul, half_sq]
  norm_num

/-- **The quarter-period gate prepares the two-support state.** -/
theorem quarter_gate_prepares (H : Matrix n n ℂ) (a b : n)
    (hab : H *ᵥ Pi.single a 1 = Pi.single b 1) :
    quarterGate H *ᵥ Pi.single a 1 = quarterState a b := by
  unfold quarterGate quarterState
  rw [smul_mulVec, add_mulVec, one_mulVec, smul_mulVec, hab]

end PMAction.CoherentPreparation
