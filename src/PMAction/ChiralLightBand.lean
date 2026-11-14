import PMAction.ChiralityConvention

/-!
# The chirality identification extends to the light band

`ChiralityConvention.projector_unique_on_kernel` forces the charged projector `(1 − Γ)/2` on the
zero kernel of the two-slice Hamiltonian at `k = 0`. Away from the kernel the Hamiltonian does not
commute with `Γ` (the mass `δβ` and the inter-slice hops anticommute with it), so the
identification needs an argument. The light modes at small momentum are governed, to first order
in `k`, by the Hamiltonian projected onto the zero-mode space (degenerate perturbation theory).

* `PZ`: the projector onto the zero kernel (`PZ_fixes_kernel`, `PZ_into_kernel`): components
  `0, 1` of the first wall and `2, 3` of the second (`ConcreteFermion.kernel_coordinates`).
* `light_block`: projected, the inter-slice hops vanish and so does `β`:
  `PZ H(k) PZ = diag(P₁ K P₁, P₂ K P₂)` with `K = Σ sin kⱼ αⱼ`.
* `light_conserves_chirality`: this effective light Hamiltonian commutes with the wall chirality
  `Γ` (`αⱼ` commutes with `γ`, `ConcreteFermion.alpha_gamma`), so the light eigenstates at small `k`
  have definite chirality, and the light dynamics never mixes the walls.
* `projector_on_light_band`: on the zero-mode space the charged projector `(1 − Γ)/2` is exactly the
  second wall's light block: it selects the second wall's light branch at every `k` in the
  effective theory.

So the identification of the charged current's wall extends from the kernel to the light band at
first order in `k`; wall mixing enters only through the gapped modes, at `O(k²/gap)`.
-/

noncomputable section
namespace PMAction.ChiralLightBand
open Matrix ConcreteFermion WallChiralCurrent

/-- First wall's zero-mode components. -/
def P1 : Spin := diagonal ![1, 1, 0, 0]
/-- Second wall's zero-mode components. -/
def P2 : Spin := diagonal ![0, 0, 1, 1]

/-- The projector onto the zero kernel. -/
def PZ : Matrix Sites Sites ℂ := fromBlocks P1 0 0 P2

theorem PZ_fixes_kernel (v : Sites → ℂ) (hv : hamiltonian 0 0 *ᵥ v = 0) : PZ *ᵥ v = v := by
  obtain ⟨h1, h2, h3, h4⟩ := (kernel_coordinates v).1 hv
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [PZ, P1, P2, mulVec, dotProduct, fromBlocks, Fintype.sum_sum_type, diagonal,
      h1, h2, h3, h4]

theorem PZ_into_kernel (v : Sites → ℂ) : hamiltonian 0 0 *ᵥ (PZ *ᵥ v) = 0 := by
  rw [kernel_coordinates]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [PZ, P1, P2, mulVec, dotProduct, fromBlocks, Fintype.sum_sum_type, diagonal]

lemma P1_hop_P2 : P1 * DomainWallSpectrum.hop beta gamma * P2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P1, P2, DomainWallSpectrum.hop, DomainWallSpectrum.plus, beta, gamma, mul_apply,
      diagonal, vecMul, dotProduct, Fin.sum_univ_four, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply]

lemma P2_back_P1 : P2 * DomainWallSpectrum.back beta gamma * P1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P1, P2, DomainWallSpectrum.back, DomainWallSpectrum.minus, beta, gamma, mul_apply,
      diagonal, vecMul, dotProduct, Fin.sum_univ_four, Matrix.sub_apply, Matrix.one_apply]

lemma P1_gamma : P1 * gamma = gamma * P1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P1, gamma, mul_apply, diagonal]

lemma P2_gamma : P2 * gamma = gamma * P2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P2, gamma, mul_apply, diagonal]

lemma K_gamma (k : Fin 3 → ℝ) :
    DomainWallSpectrum.momentum alpha k * gamma = gamma * DomainWallSpectrum.momentum alpha k :=
  (DomainWallSpectrum.kinetic_relations alpha beta gamma k clifford alpha_gamma).2.2

/-- **The light block.** Projected onto the zero modes, the hops between the slices and `β` drop
out. -/
theorem light_block (k : Fin 3 → ℝ) :
    PZ * hamiltonian k 0 * PZ =
      fromBlocks (P1 * DomainWallSpectrum.momentum alpha k * P1) 0 0
        (P2 * DomainWallSpectrum.momentum alpha k * P2) := by
  rw [hamiltonian, DomainWallSpectrum.H, PZ, fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_smul, add_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add]
  rw [P1_hop_P2, P2_back_P1]

lemma conj_commute {P K : Spin} (hP : P * gamma = gamma * P) (hK : K * gamma = gamma * K) :
    P * K * P * gamma = gamma * (P * K * P) := by
  calc P * K * P * gamma = P * (K * (P * gamma)) := by simp only [mul_assoc]
    _ = P * (K * (gamma * P)) := by rw [hP]
    _ = P * ((K * gamma) * P) := by simp only [mul_assoc]
    _ = P * ((gamma * K) * P) := by rw [hK]
    _ = (P * gamma) * (K * P) := by simp only [mul_assoc]
    _ = (gamma * P) * (K * P) := by rw [hP]
    _ = gamma * (P * K * P) := by simp only [mul_assoc]

/-- **The light dynamics conserves wall chirality.** -/
theorem light_conserves_chirality (k : Fin 3 → ℝ) :
    PZ * hamiltonian k 0 * PZ * chirality = chirality * (PZ * hamiltonian k 0 * PZ) := by
  rw [light_block, chirality, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [conj_commute P1_gamma (K_gamma k), conj_commute P2_gamma (K_gamma k)]

/-- **On the light band the charged projector is the second wall's block.** -/
theorem projector_on_light_band : projector * PZ = fromBlocks 0 0 0 P2 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [projector, chirality, PZ, P1, P2, gamma, fromBlocks, mul_apply, Fintype.sum_sum_type,
      diagonal, Matrix.sub_apply, Matrix.one_apply] <;> norm_num

end PMAction.ChiralLightBand
