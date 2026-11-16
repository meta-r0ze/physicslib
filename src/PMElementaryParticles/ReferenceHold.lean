import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Holding the reference: the one antipode-odd step, and what it does to the wire

`CycleReadout`: a protocol readout that departs from the wire's spectrum needs a step with an
odd/even block, and the only antipode-odd object is the reference carrier `r = +2e₀` (vector
class, lepton axis, reference wall). Here is the step persistence forces.

**Premise (persistence of the reference).** The reference persists: it is held as a fixed record
every tick. Amplitude moved into or out of `r` would change the reference, so the dynamics of
everything else acts on the complement of `r`: the cycle is compressed by `Q = 1 − |r⟩⟨r|`.

On the reference's slot (lepton axis, heavy label, reference wall) the doublet space is
`span {o, e}` (odd wire mode, even complement), `r = (o + e)/√2`, and the electron channel is
`c = (o − e)/√2 = S r` (`S` the antipode).

* `hold_not_commute`: `Q` does not commute with the antipode `S = diag(−1, 1)`: it is the
  antipode-odd step `CycleReadout` requires.
* `hold_odd`: `Q o = c/√2` (in coordinates `(1/2, −1/2)`): after the hold, the wire mode on the
  reference's slot survives only as the electron channel, with amplitude `1/√2`.
* `hold_row`: so on that slot the wire's row is scaled by `1/√2`: for the lepton protocols the
  wire's mass is `diag(1/√2, 1, 1) · M` (rows are the reference wall). The neutral protocol's
  heavy-label channel on the reference wall is `r` itself and is not available to it.

**Test (numerical, `δ_O` complex per protocol, `K = 1`, `k = α/2`).** Without the hold the lepton
protocol's best `(m_e/m_μ, m_μ/m_τ)` is `(0.0059, 0.028)`; with the hold `(0.0053, 0.038)`, against
`(0.00484, 0.0595)`. The hold moves the second ratio the right way but does not reach the data. The
colour axes carry no reference, so the up and down protocols are unchanged (up `m_c/m_t`: `0.022`
against `0.0037`). So the steps persistence fixes today (wire, refresh, colour maintenance, the
reference hold) do not give the masses; with the hold's odd/even block the even complement's own
action now enters the readout (through `e` in `c`), and is the remaining input.
-/

namespace PMElementaryParticles.ReferenceHold
open Matrix

/-- The reference on its slot, in the `(odd, even)` basis: `(1, 1)/√2`. -/
noncomputable def r : Fin 2 → ℝ := ![1 / Real.sqrt 2, 1 / Real.sqrt 2]

/-- The hold: `Q = 1 − |r⟩⟨r|`. -/
noncomputable def Q : Matrix (Fin 2) (Fin 2) ℝ := 1 - vecMulVec r r

/-- The antipode on the slot. -/
def S : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

lemma inv_sqrt_two_sq : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]

theorem Q_eq : Q = !![1 / 2, -1 / 2; -1 / 2, 1 / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Q, r] <;> norm_num [inv_sqrt_two_sq] <;>
    rw [← one_div, inv_sqrt_two_sq] <;> norm_num

theorem hold_not_commute : Q * S ≠ S * Q := by
  rw [Q_eq]; intro h
  have := congrFun (congrFun h 0) 1
  simp [S, Matrix.mul_apply, Fin.sum_univ_two] at this
  norm_num at this

theorem hold_odd : Q *ᵥ ![1, 0] = ![1 / 2, -1 / 2] := by
  rw [Q_eq]; ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- The held odd mode is `c/√2`, with `c = (1, −1)/√2` the electron channel. -/
theorem hold_row : Q *ᵥ ![1, 0] =
    (1 / Real.sqrt 2) • ![1 / Real.sqrt 2, -(1 / Real.sqrt 2)] := by
  rw [hold_odd]; ext i; fin_cases i <;> simp <;>
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

end PMElementaryParticles.ReferenceHold
