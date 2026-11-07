import PMFlavor.WallImpedanceChoice
import PMFlavor.TransferFlavor

/-! **Experimental/candidate module.**

# Capacity impedance

The capacity impedance is the zero-momentum mass ratio.  With mass ratio
`(16/21)^2` it equals the transfer impedance `16/21`.
-/

noncomputable section
namespace PMFlavor.CapacityImpedance

open PMFlavor.WallImpedanceChoice PMFlavor.TransferFlavor

/-- Squared mass ratio selected by the capacity split. -/
def capacityMassRatio : ℝ := 256 / 441

theorem capacityMassRatio_eq_sq : capacityMassRatio = (16 / 21 : ℝ) ^ 2 := by
  norm_num [capacityMassRatio]

/-- With the capacity mass ratio, the impedance is `16/21`. -/
theorem capacityImpedance_eq :
    capacityImpedance ((16 / 21 : ℝ) ^ 2) 1 = 16 / 21 := by
  unfold capacityImpedance
  rw [show ((16 / 21 : ℝ) ^ 2) / 1 = (16 / 21) ^ 2 by ring]
  exact Real.sqrt_sq (by norm_num)

/-- The capacity impedance agrees with the transfer impedance. -/
theorem capacityImpedance_eq_transfer :
    capacityImpedance ((16 / 21 : ℝ) ^ 2) 1 = transferImpedance := by
  rw [capacityImpedance_eq]
  norm_num [transferImpedance, ckmCapacity, pmnsCapacity]

theorem capacityImpedance_pos : 0 < capacityImpedance ((16 / 21 : ℝ) ^ 2) 1 := by
  rw [capacityImpedance_eq]
  norm_num

end PMFlavor.CapacityImpedance
