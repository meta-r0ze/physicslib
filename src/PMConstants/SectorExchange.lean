import PMConstants.HermitianMass
import Mathlib.Data.Matrix.Block

/-!
# Sector exchange makes the link mass Hermitian; one doublet's phase cancels in θ̄

`HermitianMass` assumed the inter-sector link matrix is Hermitian. This module reduces that to a
symmetry of the update and removes the remaining phase.

* `exchange_hermitian`: write the update's generator on the two sectors as the block matrix
  `H = [[A, M], [M', B]]` (`M` hops sector 2 → 1). If `H` is Hermitian (the update is unitary) and
  commutes with the exchange `S = [[0, 1], [1, 0]]`, then `M = M†` (and `A = B`).
  The exchange is combined with parity: it maps the left-handed states of one sector to the
  right-handed states of the other, so the domain wall's orientation (a property of the vacuum,
  not of the update) is not an obstruction.
* `one_doublet_phase_cancels`: with a single link doublet of vacuum value `v`, the up-type masses
  use `v̄` and the down-type masses use `v`. For three generations
  `det(v̄ Y_u) det(v Y_d) = |v|⁶ det Y_u det Y_d`, so the vacuum phase drops out of `θ̄`.
* `thetaBar_zero`: for Hermitian, positive `Y_u, Y_d`, `v ≠ 0` and `θ = 0`, `θ̄ = 0`.

Premise, now stated as a symmetry: the update carries no sector label. The two sectors are the
same D₄ (Paper I's `d4d4`), and a label that no observable requires is a spare coordinate,
which Economy (`FinalPremises.description_minimal`) excludes. This is an argument from Paper I's
premises, not a formal derivation here.
-/

noncomputable section
namespace PMConstants.SectorExchange
open Matrix Complex ComplexConjugate HermitianMass

variable {n : Type*} [Fintype n] [DecidableEq n]

def swap : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 0 1 1 0

theorem exchange_hermitian (A M M' B : Matrix n n ℂ)
    (hH : (fromBlocks A M M' B)ᴴ = fromBlocks A M M' B)
    (hS : swap * fromBlocks A M M' B * swap = fromBlocks A M M' B) :
    Mᴴ = M ∧ A = B := by
  rw [fromBlocks_conjTranspose, fromBlocks_inj] at hH
  simp only [swap, fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero,
    Matrix.mul_one, zero_add, add_zero, fromBlocks_inj] at hS
  obtain ⟨_, _, h3, h4⟩ := hS
  obtain ⟨_, _, k3, _⟩ := hH
  exact ⟨k3.trans h3.symm, h4⟩

theorem one_doublet_phase_cancels (v : ℂ) (Yu Yd : Matrix (Fin 3) (Fin 3) ℂ) :
    (conj v • Yu).det * (v • Yd).det =
      ((Complex.normSq v ^ 3 : ℝ) : ℂ) * (Yu.det * Yd.det) := by
  rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin]
  have : (conj v)^3 * v^3 = ((Complex.normSq v ^ 3 : ℝ) : ℂ) := by
    rw [← mul_pow, mul_comm, Complex.mul_conj]; push_cast; ring
  linear_combination (Yu.det * Yd.det) * this

theorem thetaBar_zero (v : ℂ) (hv : v ≠ 0) {Yu Yd : Matrix (Fin 3) (Fin 3) ℂ}
    (hu : Yu.IsHermitian) (hd : Yd.IsHermitian)
    (pu : ∀ i, 0 < hu.eigenvalues i) (pd : ∀ i, 0 < hd.eigenvalues i) :
    thetaBar 0 (conj v • Yu) (v • Yd) = 0 := by
  obtain ⟨u1, u2⟩ := det_pos_of_hermitian hu pu
  obtain ⟨d1, d2⟩ := det_pos_of_hermitian hd pd
  have hn : 0 < Complex.normSq v ^ 3 := pow_pos (Complex.normSq_pos.mpr hv) 3
  unfold thetaBar
  rw [one_doublet_phase_cancels, u1, d1, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.arg_ofReal_of_nonneg (by positivity), sub_zero]

end PMConstants.SectorExchange
