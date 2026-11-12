import PMAction.VATrace
import PMAction.D4Isotropy
import PMAction.LoopMeasure

/-!
# The one-loop running of the charged-current contact

`WeakVertex` gives the charged-current contact `(G/√2)[ψ̄₁γ^μ(1−γ⁵)ψ₂][ψ̄₃γ_μ(1−γ⁵)ψ₄]` at the
W/Z scale. Between that scale and the decay scale, photon exchange among the four charged legs
rescales the contact's amplitude by `1 + c·(α/4π)·ln(M²/μ²)`. This module derives the coefficient
`c` from the Dirac algebra of Paper II's matrices and the leg charges, leaving one normalization
as input (see below).

**The three kinds of photon exchange.**
* Within one bilinear (legs `1,2` or `3,4`): the vertex exchange and the two legs' self-energies
  combine as `Q₁Q₂·(−W) + ½(Q₁² + Q₂²)·W = ½W(Q₁ − Q₂)²` (`ward_combination`). The vertex weight
  is `−W` because a conserved current (`Q₁ = Q₂`) is not renormalized (the Ward identity). The
  vertex's Dirac factor is the contraction `γ^σγ^μγ_σ = −2γ^μ` (`contraction`).
* Between bilinears, same orientation (legs `1,3` and `2,4`): the loop momentum gives
  `¼ γ^ργ^σΓ ⊗ γ_ργ_σΓ`, and with `Γ = γ^μ(1−γ⁵)` this is `16 Γ ⊗ Γ`.
* Between bilinears, opposite orientation (legs `1,4` and `2,3`): `¼ γ^ργ^σΓ ⊗ Γγ_σγ_ρ = 4 Γ ⊗ Γ`,
  with the opposite sign (one leg's fermion flow is reversed).

The two tensor identities (`16`, `4`) are proved in `ContactFierz` on the 2×2 Weyl blocks of
these matrices (`same_identity'`, `opp_identity`), with the reduction from the 4×4 form to the
blocks in `ContactFierz.triple_blk`.

**Result.** With `W = −1` (in units of `α/4π · ln(M²/μ²)`):
`c = −½(Q₁−Q₂)² − ½(Q₃−Q₄)² − 4(Q₁Q₃ + Q₂Q₄) + (Q₁Q₄ + Q₂Q₃)` (`contactCoefficient`).
* `contact_semileptonic`: for a lepton pair `(−1, 0)` and quarks `(Q, Q − 1)`, `c = 3Q`, which is
  `(3/2)(1 + 2Q̄)` with `Q̄ = (Q₁ + Q₂)/2`. The constant parts cancel exactly.
* `contact_neutron`: with Paper V's carrier charges `2/3`, `−1/3`, `c = 2`.
* `rate_factor`: the rate gets `1 + 2c(α/4π)ln(M²/μ²) = 1 + (3α/4π)(1 + 2Q̄)ln(M²/μ²)`, the form
  `PMHadrons.ShortDistanceRunning` uses.

**The `¼` is the substrate's.** Averaging the loop momentum's `k^ρk^σ` over directions gives
`¼ δ^{ρσ} k²`. On the substrate the directions are the 24 D₄ link roots, and their second moment
is exactly isotropic (`D4Isotropy.second_moment`), so `4 Σ k_μk_ν = (Σ k²) δ_{μν}`
(`loop_direction_average`): the `¼` follows from the D₄ geometry.

**The normalization.** The unit `(α/4π)·ln(M²/μ²)` is the 4D measure between the two scales
(`LoopMeasure.log_unit`: `|S³|/(2π)⁴ = 1/(8π²)` times `e² = 4πα`), and the self-energy weight
`W = −1` is the contraction `−2` times the Feynman-parameter average `½`
(`LoopMeasure.self_energy_weight`).

**The orientation sign.** A photon of loop momentum `k` leaves one leg and enters the other, so
the two legs' propagator numerators carry `η_i k̸` and `−η_j k̸`, with `η = +1` for an outgoing
(`ψ̄`) leg and `−1` for an incoming (`ψ`) leg: the pair's sign is `−η_iη_j` (`orientation_sign`).
Legs `1,3` (both `ψ̄`) and `2,4` (both `ψ`) get `−`; legs `1,4` and `2,3` get `+`. This is the
sign in `sameWeight` and `oppositeWeight` (`weights_from_orientation`).

What is still the continuum's: the Feynman parametrization step itself and the identification of
the leading log region with the lattice sum far below the cutoff. These are the photon loop's log coefficient. In the
substrate this would be the response of the link field to a pair of charged legs, the analogue
of `RunningResponse`'s Landau-sum derivation of the vacuum-polarization coefficient.
-/

noncomputable section
namespace PMAction.ContactRunning
open Matrix VATrace

set_option maxHeartbeats 4000000 in
/-- **The vertex contraction.** `Σ_σ η_σ γ^σ γ^μ γ^σ = −2 γ^μ` with Paper II's matrices. -/
theorem contraction (μ : Fin 4) : ∑ σ, η σ • (g σ * g μ * g σ) = (-2 : ℂ) • g μ := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [g, η, Fin.sum_univ_four, Matrix.mul_apply, Matrix.sum_apply] <;> norm_num <;> ring

/-- **The direction average from the D₄ roots.** Over the substrate's link directions,
`4 Σ_k k_μ k_ν = (Σ_k |k|²) δ_{μν}`: the loop momentum's `k^ρ k^σ` averages to `¼ |k|² δ^{ρσ}`. -/
theorem loop_direction_average (μ ν : Fin 4) :
    4 * ∑ k ∈ D4Gauge.roots, D4Gauge.vec k μ * D4Gauge.vec k ν =
      (∑ k ∈ D4Gauge.roots, ∑ ρ, D4Gauge.vec k ρ * D4Gauge.vec k ρ) * D4Isotropy.δ μ ν := by
  revert μ ν
  decide +kernel

/-- Vertex plus self-energies within one bilinear: the Ward-identity combination. -/
theorem ward_combination (Q₁ Q₂ W : ℝ) :
    Q₁ * Q₂ * (-W) + (Q₁ ^ 2 + Q₂ ^ 2) / 2 * W = W / 2 * (Q₁ - Q₂) ^ 2 := by
  ring

/-- Same-orientation and opposite-orientation exchange weights: `¼·16` and `¼·4`, with opposite
signs. -/
def sameWeight : ℝ := -(1 / 4 * 16)
def oppositeWeight : ℝ := 1 / 4 * 4

/-- The sign of a photon exchange between legs with orientations `ηᵢ, ηⱼ` (`+1` for `ψ̄`, `−1`
for `ψ`): the numerators carry `ηᵢ k̸` and `−ηⱼ k̸`. -/
def pairSign (ηi ηj : ℝ) : ℝ := ηi * (-ηj)

theorem orientation_sign (ηi ηj : ℝ) : pairSign ηi ηj = -(ηi * ηj) := by
  unfold pairSign; ring

/-- The two cross-bilinear weights are `pairSign · ¼ · (Dirac factor)`: same orientation
(`η = (1, 1)` or `(−1, −1)`, factor `16`) and opposite orientation (`(1, −1)`, factor `4`). -/
theorem weights_from_orientation :
    sameWeight = pairSign 1 1 * (1 / 4) * 16 ∧ sameWeight = pairSign (-1) (-1) * (1 / 4) * 16 ∧
      oppositeWeight = pairSign 1 (-1) * (1 / 4) * 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [sameWeight, oppositeWeight, pairSign]

/-- The amplitude coefficient, in units of `(α/4π)·ln(M²/μ²)`, with `W = −1`. -/
def contactCoefficient (Q₁ Q₂ Q₃ Q₄ : ℝ) : ℝ :=
  (-1) / 2 * (Q₁ - Q₂) ^ 2 + (-1) / 2 * (Q₃ - Q₄) ^ 2 +
    sameWeight * (Q₁ * Q₃ + Q₂ * Q₄) + oppositeWeight * (Q₁ * Q₄ + Q₂ * Q₃)

/-- **The semileptonic coefficient.** Lepton pair `(−1, 0)`, quark pair `(Q, Q − 1)`:
`c = 3Q = (3/2)(1 + 2Q̄)`. -/
theorem contact_semileptonic (Q : ℝ) :
    contactCoefficient Q (Q - 1) (-1) 0 = 3 / 2 * (1 + 2 * ((Q + (Q - 1)) / 2)) := by
  unfold contactCoefficient sameWeight oppositeWeight
  ring

theorem contact_neutron : contactCoefficient (2 / 3) (-1 / 3) (-1) 0 = 2 := by
  unfold contactCoefficient sameWeight oppositeWeight
  norm_num

/-- The rate factor: twice the amplitude coefficient. -/
theorem rate_factor (α L Q : ℝ) :
    1 + 2 * contactCoefficient Q (Q - 1) (-1) 0 * (α / (4 * Real.pi)) * L =
      1 + 3 * α / (4 * Real.pi) * (1 + 2 * ((Q + (Q - 1)) / 2)) * L := by
  rw [contact_semileptonic]
  ring

end PMAction.ContactRunning
