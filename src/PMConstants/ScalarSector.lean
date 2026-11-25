import PMConstants.PersistentGain
import PMConstants.JointConstants

/-!
# The persistent scalar gain and scalar mass relation

`lambda_insensitive` bounds the gain for reflection charge rates
`0 < c ≤ 10000`. `higgsSq` reads the scalar mass squared at a supplied
Fermi coupling. The measured comparison is in `E8PConstants.ScalarAccounting`.
-/

noncomputable section
namespace PMConstants.ScalarSector
open PMConstants PersistentGain

theorem lambda_insensitive {c : ℝ} (hc : 0 < c) (hc' : c ≤ 10000) :
    ∃ gs, Persistent c gs ∧ (∀ g, Persistent c g → g ≤ gs) ∧ gs < selfCoupling ∧
      selfCoupling - gs < 0.0000044 := by
  obtain ⟨gs, hp, hmax, -, hlt, hd⟩ := persistent_maximum hc
  refine ⟨gs, hp, hmax, hlt, ?_⟩
  have : c * 0.00000001 / 23 ≤ 10000 * 0.00000001 / 23 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
  linarith [show (10000 : ℝ) * 0.00000001 / 23 < 0.0000044 by norm_num]

/-- `m_H² = 2λ v_F²` with `v_F² = 1/(√2 G_F)`. -/
def higgsSq (GF : ℝ) : ℝ := 2 * selfCoupling / (Real.sqrt 2 * GF)

end PMConstants.ScalarSector
