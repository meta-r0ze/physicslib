import PMFlavor.WallMassModel

/-! **Experimental/candidate module.**

# Impedance convention

The capacity impedance `16/21` is a zero-momentum mass ratio.  The physical
energy-ratio impedance `wallImpedanceAt p m0 m2` is a separate diagnostic.  They
need not agree at the preparation momentum.
-/

noncomputable section
namespace PMFlavor.WallImpedanceChoice

open PMFlavor.WallMassModel

inductive ImpedanceConvention
  | zeroMomentumMassRatio
  | physicalEnergyRatio
  deriving DecidableEq, Repr

/-- Capacity/mass-ratio impedance. -/
def capacityImpedance (m0 m2 : ℝ) : ℝ := Real.sqrt (m0 / m2)

/-- Physical energy-ratio impedance. -/
def physicalImpedance (p m0 m2 : ℝ) : ℝ := wallImpedanceAt p m0 m2

/-- The selected convention for the capacity calculation. -/
def selectedConvention : ImpedanceConvention := .zeroMomentumMassRatio

end PMFlavor.WallImpedanceChoice
