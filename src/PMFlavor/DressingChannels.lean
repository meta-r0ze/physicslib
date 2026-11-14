import PMFlavor.CKMDressing

/-!
# The channels that carry the `1/688`: exactly three, the spatial axes

`CKMDressing.dilation_needs_three`: a uniformly dressed block `A = qV` (`AAᴴ = q²·1`, `q² ≠ 1`)
inside a unitary needs at least three extra channels. Here the bound is attained.

* `dilation_three`: for unitary `V` and `q² + p² = 1`, the block matrix
  `W = [[q V, p 1], [p 1, −q Vᴴ]]` is unitary, with `qV` as its upper-left block. So **three extra
  channels suffice**, and with `dilation_needs_three` the minimal count is exactly `3`.
* In this dilation row `i` loses `p²` into extra channel `i` alone: each generation row leaks into
  its own channel.

Economy (no spare channel, `PMSubstrate.FinalPremises.description_minimal`) takes the minimal
dilation, so the dressing needs exactly three outlets. The substrate already has exactly three
outlets of that kind: the `D − 1` spatial axes on which readout transfers land
(`PMConstants.VevEvent`, `VevLedger.noiseDenominator_eq_orthogonal`), the same channels as the
reactor angle's node conductance (`ReactorConductance`). That identification is the reading; the
count `3 = D − 1` is checked.

**What it says about the divisor.** Three rows each lose `ε` into the three spatial channels, so
the block loses `3ε = (D − 1) ε` in all. The reference deficit is `1 − η = 1/172` per frame
(`PMConstants.FlavourDressing`). The two divisors the data allow (`CabibboDressing.direction_shares_fit`)
are the two ways that deficit can reach the spatial channels:
* `ε = (1 − η)/D = 1/688`: the deficit is shared over all `D` directions and only the `D − 1`
  spatial shares leave (`total_if_spatial_shares`); the temporal share stays with the reference.
* `ε = (1 − η)/(D − 1) = 1/516`: the whole deficit leaves through the spatial channels
  (`total_if_whole`).
So the open question is now physical: does the temporal direction's share of the reference deficit
leave the CKM block or not. Not settled here.
-/

namespace PMFlavor.DressingChannels
open Matrix

/-- The minimal dilation of a uniformly dressed unitary. -/
noncomputable
def W (V : Matrix (Fin 3) (Fin 3) ℂ) (q p : ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ :=
  fromBlocks (q • V) (p • (1 : Matrix (Fin 3) (Fin 3) ℂ)) (p • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    ((-q) • Vᴴ)

theorem dilation_three (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : V * Vᴴ = 1) (q p : ℝ)
    (h : q ^ 2 + p ^ 2 = 1) : W V q p * (W V q p)ᴴ = 1 ∧ (W V q p).toBlocks₁₁ = q • V := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  refine ⟨?_, by simp [W]⟩
  rw [W, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  simp only [conjTranspose_smul, star_trivial, conjTranspose_conjTranspose, conjTranspose_one,
    smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hV, hV']
  congr 1
  · rw [← add_smul]; convert one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℂ) using 2; nlinarith
  · rw [← add_smul]; convert zero_smul ℝ V using 2; ring
  · rw [← add_smul]; convert zero_smul ℝ Vᴴ using 2; ring
  · rw [← add_smul]; convert one_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℂ) using 2; nlinarith

theorem total_if_spatial_shares :
    (3 : ℝ) * ((1 / 172) / 4) = (4 - 1) / 4 * (1 / 172) ∧ (1 / 172 : ℝ) / 4 = 1 / 688 := by
  norm_num

theorem total_if_whole : (3 : ℝ) * ((1 / 172) / 3) = 1 / 172 ∧ (1 / 172 : ℝ) / 3 = 1 / 516 := by
  norm_num

end PMFlavor.DressingChannels
