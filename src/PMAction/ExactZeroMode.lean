import PMAction.CompositeMass

/-!
# The resonance zero mode is exact on the full two-wall Hamiltonian

`OtherWallStationary`: economy puts the other wall's flip on the cycle resonance, where the light
mass `M = D₂ Y⁻¹ D₁ᴴ` has a null vector (`massless_iff`), for any reference-wall carriers and any
protocol weight on the heavy label. `M` is the zero-energy Schur complement of the full Hamiltonian
`H = [[0, V], [Vᴴ, G]]` (light modes, gapped modes; `CompositeMass.effective_mass_general`), so its
null vector is not only a leading-order statement:

* `exact_zero_mode`: if `M v = 0` with `v ≠ 0` and the crossing link `Y` invertible, then
  `w = (x, −G⁻¹ Vᴴ x)` with `x = (v, 0)` is a nonzero exact zero mode of `H`.

So at the resonance the lightest state of every protocol is exactly massless on the wire, to all
orders in the light–gapped coupling. A nonzero lightest mass (`m_e`, `m_u`, `m_d`) is not a
higher-order wire effect: it needs the flip off the resonance, which the stationary selection
excludes, or a term from the protocol register (PMElementaryParticles REVIEW, "Light masses").
-/

noncomputable section
namespace PMAction.ExactZeroMode
open Matrix PMAction.WallSeesaw PMAction.CompositeMass

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The full Hamiltonian: light modes coupled by `V2 D₁ D₂` to the gapped crossing block `G Y`. -/
def H (Y D₁ D₂ : Matrix n n ℂ) : Matrix ((n ⊕ n) ⊕ (n ⊕ n)) ((n ⊕ n) ⊕ (n ⊕ n)) ℂ :=
  fromBlocks 0 (V2 D₁ D₂) (V2 D₁ D₂)ᴴ (G Y)

/-- **A null vector of the light mass is an exact zero mode of the full Hamiltonian.** -/
theorem exact_zero_mode (Y D₁ D₂ : Matrix n n ℂ) (hY : IsUnit Y.det) (v : n → ℂ) (hv : v ≠ 0)
    (hM : (D₂ * Y⁻¹ * D₁ᴴ) *ᵥ v = 0) :
    ∃ w, w ≠ 0 ∧ H Y D₁ D₂ *ᵥ w = 0 := by
  obtain ⟨hGG, -⟩ := gapped_inverse Y hY
  set x : n ⊕ n → ℂ := Sum.elim v 0 with hx
  set z := -(Ginv Y *ᵥ ((V2 D₁ D₂)ᴴ *ᵥ x)) with hz
  refine ⟨Sum.elim x z, ?_, ?_⟩
  · intro h
    apply hv
    funext i
    have := congrFun h (Sum.inl (Sum.inl i))
    simpa [hx] using this
  · have heff : -(V2 D₁ D₂ * Ginv Y * (V2 D₁ D₂)ᴴ) *ᵥ x = 0 := by
      rw [effective_mass_general, hx]
      ext i; rcases i with i | i
      · simp [fromBlocks_mulVec]
      · simpa [fromBlocks_mulVec] using congrFun hM i
    have hG : G Y *ᵥ z = -((V2 D₁ D₂)ᴴ *ᵥ x) := by
      rw [hz, mulVec_neg, mulVec_mulVec, hGG, one_mulVec]
    rw [H, fromBlocks_mulVec]
    ext i; rcases i with i | i
    · have h1 : V2 D₁ D₂ *ᵥ z = -(V2 D₁ D₂ * Ginv Y * (V2 D₁ D₂)ᴴ) *ᵥ x := by
        rw [hz, mulVec_neg, neg_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
      simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add,
        Pi.zero_apply]
      rw [h1, heff]; rfl
    · simp only [Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply, Pi.add_apply]
      rw [hG]; simp

end PMAction.ExactZeroMode
