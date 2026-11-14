import Mathlib.Tactic

/-!
# What a `θ₂₃` construction must supply: a common wall factor cancels

`θ₂₃`'s deviation from maximal is the lepton `s`/`c` parity breaking (`ExchangeChirality`). It is
read from the third neutrino state's charged-current strengths into the `μ` and `τ` readouts:
`asym_is_theta23`: for a unitary third column `(s₁₃, s₂₃c₁₃, c₂₃c₁₃)` the normalized asymmetry
`(W_μ − W_τ)/(W_μ + W_τ)` is `2 sin²θ₂₃ − 1`, with `c₁₃²` cancelling (NuFIT 6.0 normal ordering:
`+0.122` without the Super-Kamiokande atmospheric data, `−0.060` with it).

The native current factorizes as `P_L ⊗ G` on both walls (`WeakCurrentBridge.modelCurrent_eq_PL`),
so a strength is a wall factor times a generation factor.
* `common_wall_cancels`: if the wall factor is the same for both readouts, the asymmetry is the
  generation factor's alone, `(G_μ − G_τ)/(G_μ + G_τ)`: a weak-wall versus spectator-wall
  asymmetry shared by both generations does not move `θ₂₃`.
* `wall_only`: if the generation factors are `μ`–`τ` symmetric (`G_μ = G_τ`, the residual `Z₂` of
  `GenerationBreaking`), the whole asymmetry is `(w_μ − w_τ)/(w_μ + w_τ)`: it needs wall overlaps
  that differ between the two readouts.

So a `θ₂₃` construction must supply either a `μ`–`τ`-asymmetric generation factor or wall overlaps
correlated with the generation readout; the wall asymmetry alone (and so the carrier's axial current
alone) does not give it.
-/

namespace PMFlavor.Theta23Wall

/-- Normalized asymmetry of two strengths. -/
noncomputable def asym (a b : ℝ) : ℝ := (a - b) / (a + b)

theorem asym_is_theta23 (s23 c23 c13 : ℝ) (h23 : s23 ^ 2 + c23 ^ 2 = 1) (hc : c13 ≠ 0) :
    asym ((s23 * c13) ^ 2) ((c23 * c13) ^ 2) = 2 * s23 ^ 2 - 1 := by
  unfold asym
  have hd : (s23 * c13) ^ 2 + (c23 * c13) ^ 2 = c13 ^ 2 := by
    rw [mul_pow, mul_pow, ← add_mul, h23, one_mul]
  rw [hd, div_eq_iff (pow_ne_zero 2 hc)]
  have : c23 ^ 2 = 1 - s23 ^ 2 := by linarith
  rw [mul_pow, mul_pow, this]; ring

theorem common_wall_cancels (w Gμ Gτ : ℝ) (hw : w ≠ 0) :
    asym (w * Gμ) (w * Gτ) = asym Gμ Gτ := by
  unfold asym
  rw [← mul_sub, ← mul_add, mul_div_mul_left _ _ hw]

theorem wall_only (wμ wτ G : ℝ) (hG : G ≠ 0) :
    asym (wμ * G) (wτ * G) = asym wμ wτ := by
  unfold asym
  rw [← sub_mul, ← add_mul, mul_div_mul_right _ _ hG]

end PMFlavor.Theta23Wall
