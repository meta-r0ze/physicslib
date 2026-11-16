import PMAction.ChiralLightBand

/-! Exact light/gapped weights for the existing chiral current.
The current retains the negative-chirality gapped component on the first wall.
Turning these weights into a protocol row deficit requires the external-state
and final-channel readout construction. -/
noncomputable section
namespace PMAction.WallCurrentWeights
open Matrix ConcreteFermion WallChiralCurrent ChiralLightBand

def lightWeight (ψ : Sites → ℂ) : ℝ :=
  Complex.normSq (ψ (.inl 0)) + Complex.normSq (ψ (.inl 1)) +
    Complex.normSq (ψ (.inr 2)) + Complex.normSq (ψ (.inr 3))

def chargedLightWeight (ψ : Sites → ℂ) : ℝ :=
  Complex.normSq (ψ (.inr 2)) + Complex.normSq (ψ (.inr 3))

def chargedGapWeight (ψ : Sites → ℂ) : ℝ :=
  Complex.normSq (ψ (.inl 2)) + Complex.normSq (ψ (.inl 3))

def oppositeGapWeight (ψ : Sites → ℂ) : ℝ :=
  Complex.normSq (ψ (.inr 0)) + Complex.normSq (ψ (.inr 1))

def gapWeight (ψ : Sites → ℂ) : ℝ := chargedGapWeight ψ + oppositeGapWeight ψ

theorem light_weight (ψ : Sites → ℂ) :
    (∑ i, Complex.normSq ((PZ *ᵥ ψ) i)) = lightWeight ψ := by
  simp [PZ, P1, P2, lightWeight, mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_four]
  ring

theorem gap_weight (ψ : Sites → ℂ) :
    (∑ i, Complex.normSq (((1-PZ) *ᵥ ψ) i)) = gapWeight ψ := by
  simp [PZ, P1, P2, gapWeight, chargedGapWeight, oppositeGapWeight,
    mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four]

theorem charged_weight (ψ : Sites → ℂ) :
    (∑ i, Complex.normSq ((projector *ᵥ ψ) i)) =
      chargedLightWeight ψ + chargedGapWeight ψ := by
  norm_num [projector, chirality, gamma, chargedLightWeight, chargedGapWeight,
    smul_mulVec, sub_mulVec, fromBlocks_mulVec, mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_four]
  ring

theorem charged_light_weight (ψ : Sites → ℂ) :
    (∑ i, Complex.normSq ((projector *ᵥ (PZ *ᵥ ψ)) i)) = chargedLightWeight ψ := by
  rw [charged_weight]
  simp [chargedLightWeight, chargedGapWeight, PZ, P1, P2,
    mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four]

theorem charged_gap_weight (ψ : Sites → ℂ) :
    (∑ i, Complex.normSq ((projector *ᵥ ((1-PZ) *ᵥ ψ)) i)) = chargedGapWeight ψ := by
  rw [charged_weight]
  simp [chargedLightWeight, chargedGapWeight, PZ, P1, P2,
    mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four]

theorem charged_gap_le_total (ψ : Sites → ℂ) : chargedGapWeight ψ ≤ gapWeight ψ := by
  unfold gapWeight oppositeGapWeight
  have h0 := Complex.normSq_nonneg (ψ (.inr 0))
  have h1 := Complex.normSq_nonneg (ψ (.inr 1))
  linarith

theorem all_gap_charged_iff (ψ : Sites → ℂ) :
    chargedGapWeight ψ = gapWeight ψ ↔ ψ (.inr 0) = 0 ∧ ψ (.inr 1) = 0 := by
  unfold gapWeight oppositeGapWeight
  constructor
  · intro h
    have h0 := Complex.normSq_nonneg (ψ (.inr 0))
    have h1 := Complex.normSq_nonneg (ψ (.inr 1))
    have hz0 : Complex.normSq (ψ (.inr 0)) = 0 := by linarith
    have hz1 : Complex.normSq (ψ (.inr 1)) = 0 := by linarith
    exact ⟨Complex.normSq_eq_zero.mp hz0, Complex.normSq_eq_zero.mp hz1⟩
  · rintro ⟨h0,h1⟩
    simp [h0,h1]

end PMAction.WallCurrentWeights
