import PMConstants.GravityAccounting
import PMConstants.CarrierRepresentation

/-! The frame boundary stores one colour-axis charge quantum per closure. -/

noncomputable section
namespace PMConstants.BoundaryStorage
open PMConstants CertifiedConstants GravityAccounting

theorem storage_is_charge_quantum : (2 : ℚ) * (1/3) = 2/3 ∧
    ∀ a b : ℚ, 3 * a + b = 0 → b = -1 → 2 * a = 2/3 := by
  refine ⟨by norm_num, fun a b htr hl => ?_⟩
  have := (CarrierRepresentation.bl_traceless a b htr hl).1
  rw [this]; norm_num

end PMConstants.BoundaryStorage
