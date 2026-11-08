import PMFlavor.PMNS
import PMFlavor.FlavourInvariants

/-! **PMNS geometry as chamber/capacity statements.**

The original Paper IV PMNS formulae are restated as explicit geometric objects:
the atmospheric angle is a maximal bisection dilated by the bulk strain of the
`ν+σ` capacity basin, and the reactor angle is the colour-remainder admittance.
The CP sign and octant are retained as explicit branch choices.
-/

noncomputable section
namespace PMFlavor.PMNSGeometry

open PMFlavor

/-- Active bulk capacity basin `ν+σ`. -/
def capacityBasin : ℕ := FlavourInvariants.nu + FlavourInvariants.sigma

theorem capacityBasin_eq : capacityBasin = 21 := by
  norm_num [capacityBasin, FlavourInvariants.nu_eq, FlavourInvariants.sigma_eq]

/-- Bare two-channel bisection. -/
def bareBisection : ℝ := 1 / FlavourInvariants.chi

/-- Bulk strain carried by the capacity basin. -/
def bulkStrain : ℝ := Real.pi / capacityBasin

/-- Dressed atmospheric squared sine. -/
def atmosSineSq : ℝ := bareBisection * (1 + bulkStrain)

theorem atmosSineSq_eq : atmosSineSq = PMNS.sineSquared 1 := by
  unfold atmosSineSq bareBisection bulkStrain capacityBasin
  rw [FlavourInvariants.chi_eq, FlavourInvariants.nu_eq, FlavourInvariants.sigma_eq]
  simp [PMNS.sineSquared]
  ring

/-- The bulk strain puts the atmospheric angle in the upper octant. -/
theorem atmos_upper_octant : (1 / 2 : ℝ) < atmosSineSq := by
  unfold atmosSineSq bareBisection bulkStrain capacityBasin
  rw [FlavourInvariants.chi_eq, FlavourInvariants.nu_eq, FlavourInvariants.sigma_eq]
  norm_num
  nlinarith [Real.pi_pos]

/-- Colour-sector remainder `σ−χ`. -/
def colourRemainder : ℕ := FlavourInvariants.sigma - FlavourInvariants.chi

theorem colourRemainder_eq : colourRemainder = 3 := by
  norm_num [colourRemainder, FlavourInvariants.sigma_eq, FlavourInvariants.chi_eq]

/-- Reactor (colour cross-talk) squared sine. -/
def reactorSineSq : ℝ := colourRemainder / CKM.αinv

theorem reactorSineSq_eq : reactorSineSq = PMNS.sineSquared 2 := by
  unfold reactorSineSq colourRemainder
  rw [FlavourInvariants.sigma_eq, FlavourInvariants.chi_eq]
  simp [PMNS.sineSquared]

/-- Atmospheric octant. -/
inductive Octant
  | lower
  | upper
  deriving DecidableEq, Repr

/-- Selected octant: the bulk strain makes it upper. -/
def selectedOctant : Octant := .upper

theorem selectedOctant_eq : selectedOctant = .upper := rfl

/-- CP sign branch. -/
inductive CPBranch
  | positiveSin
  | negativeSin
  deriving DecidableEq, Repr

/-- The reference sum rule is used on the `sin δ < 0` branch. -/
def selectedCPBranch : CPBranch := .negativeSin

theorem selectedCPBranch_eq : selectedCPBranch = .negativeSin := rfl

end PMFlavor.PMNSGeometry
