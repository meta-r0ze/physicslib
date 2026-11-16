import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Basic.Complex.Basic
import PMElementaryParticles.DoubletSign

/-!
# One refresh cycle on a doublet: the readout needs an antipode-odd coupling

A weak pair shares one wire mode per axis and label: its states live in `odd ⊕ even`, the
antipodally odd modes (the wire's vacuum sector) and their even complement (`DoubletSign`). The
antipode acts as `S = −1 ⊕ 1`. The weak refresh is the antipode on the pair
(`DoubletSign.weak_partner_is_antipode`).

What persists over one tick is a stationary state of the cycle `U = R · W` (wire, then refresh).

* `commute_iff_block`: an operator commutes with `S` iff it has no odd/even blocks.
* `cycle_block`: if the wire step `W` commutes with `S` (any even action `E`, not only the inert
  one), the cycle is `(−W_odd) ⊕ E`.
* `cycle_charpoly`: its characteristic polynomial is `charpoly(−W_odd) · charpoly(E)`. So the
  odd sector's stationary states and phases are those of the wire step alone: the one-cycle
  readout equals the direct readout of the wire's spectrum (up to the refresh sign), which
  `PMAction.WireLightBound` and the numerical scans exclude for the up and lepton protocols.
* `cycle_pow`: the same holds over any number of cycles.

**Consequence.** Every native word commutes with the antipode
(`DoubletSign.words_commute_antipode`), and so does the refresh. A protocol readout that differs
from the wire's spectrum therefore needs an ingredient that does not commute with `S`, i.e. an
odd/even block. The only antipode-odd object in the setup is the reference carrier
(`CarrierParity.no_fixed_antipode`, `ProtocolReadout.reference_reading`). So the protocol readout
must pass through the reference's maintenance; no choice of even-complement action that commutes
with the antipode can supply it.
-/

namespace PMElementaryParticles.CycleReadout
open Matrix

variable {o e : Type*} [Fintype o] [Fintype e] [DecidableEq o] [DecidableEq e]

/-- The antipode on `odd ⊕ even`. -/
def S : Matrix (o ⊕ e) (o ⊕ e) ℂ := fromBlocks (-1) 0 0 1

theorem commute_iff_block (A : Matrix o o ℂ) (B : Matrix o e ℂ) (C : Matrix e o ℂ)
    (D : Matrix e e ℂ) :
    fromBlocks A B C D * S = S * fromBlocks A B C D ↔ B = 0 ∧ C = 0 := by
  simp only [S, fromBlocks_multiply, mul_neg, mul_one, neg_mul, one_mul, fromBlocks_inj]
  constructor
  · rintro ⟨-, hB, hC, -⟩
    refine ⟨?_, ?_⟩
    · simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add] at hB
      have : (2 : ℂ) • B = 0 := by rw [two_smul]; nth_rewrite 1 [hB]; simp
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    · simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add,
        Matrix.mul_neg, Matrix.mul_one] at hC
      have : (2 : ℂ) • C = 0 := by rw [two_smul]; nth_rewrite 2 [← hC]; simp
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  · rintro ⟨rfl, rfl⟩
    simp

/-- One cycle: the wire step `W = W_odd ⊕ E`, then the refresh `S`. -/
theorem cycle_block (Wo : Matrix o o ℂ) (E : Matrix e e ℂ) :
    S * fromBlocks Wo 0 0 E = fromBlocks (-Wo) 0 0 E := by
  simp [S, fromBlocks_multiply]

theorem cycle_charpoly (Wo : Matrix o o ℂ) (E : Matrix e e ℂ) :
    (S * fromBlocks Wo 0 0 E).charpoly = (-Wo).charpoly * E.charpoly := by
  rw [cycle_block, charpoly_fromBlocks_zero₁₂]

theorem cycle_pow (Wo : Matrix o o ℂ) (E : Matrix e e ℂ) (n : ℕ) :
    (S * fromBlocks Wo 0 0 E) ^ n = fromBlocks ((-Wo) ^ n) 0 0 (E ^ n) := by
  rw [cycle_block]
  induction n with
  | zero => simp [fromBlocks_one]
  | succ n ih => rw [pow_succ, ih, fromBlocks_multiply, pow_succ, pow_succ]; simp

end PMElementaryParticles.CycleReadout
