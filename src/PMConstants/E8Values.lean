import PMConstants.Partition
import PMSubstrate.E8Values

/-!
# The partition constants as E8 values

`Partition` states the paper's constants with decimal/rational literals. This
module gives the same quantities in terms of the forced substrate record
`baseline = ⟨D, Δ, ν, σ, χ⟩` and proves the two forms agree.

The literals are therefore values of the E8 record, not independent choices:

* `overhead = (R_M − 1)/R_M`, with `R_M = D·Δ`;
* `strongCoupling = (ν·η + 1/D)·α`;
* `footprint = R_M + ν·η + σ`;
* `clockRatio = Δ/footprint`;
* `selfCoupling = ((σ − χ) − 1/Δ)/(ν + σ + χ)`;
* `residual = ν − χ/(σ − χ) − α`.

The bridge theorems are `overhead_eq`, `strongCoupling_eq`, `footprint_eq`,
`clockRatio_eq`, `selfCoupling_eq`, `scalarToll_eq`, and `residual_eq`.
-/

noncomputable section
namespace PMConstants.E8Values
open PMSubstrate

abbrev D : ℕ := PMSubstrate.E8Values.D
abbrev Delta : ℕ := PMSubstrate.E8Values.Delta
abbrev nu : ℕ := PMSubstrate.E8Values.nu
abbrev sigma : ℕ := PMSubstrate.E8Values.sigma
abbrev chi : ℕ := PMSubstrate.E8Values.chi
abbrev RM : ℕ := PMSubstrate.E8Values.RM

theorem D_eq : D = 4 := PMSubstrate.E8Values.D_eq
theorem Delta_eq : Delta = 43 := PMSubstrate.E8Values.Delta_eq
theorem nu_eq : nu = 16 := PMSubstrate.E8Values.nu_eq
theorem sigma_eq : sigma = 5 := PMSubstrate.E8Values.sigma_eq
theorem chi_eq : chi = 2 := PMSubstrate.E8Values.chi_eq
theorem RM_eq : RM = 172 := PMSubstrate.E8Values.RM_eq

/-- The one-reserved-cell overhead, written with the E8 frame size. -/
abbrev overhead : ℝ := PMSubstrate.E8Values.overhead

/-- `(ν·η + 1/D)·α`, not `(16η + 1/4)·α` by hand. -/
def strongCoupling (α : ℝ) : ℝ := ((nu : ℝ) * overhead + 1 / (D : ℝ)) * α

/-- `R_M + ν·η + σ`, not `172 + 16η + 5`. -/
def footprint : ℝ := (RM : ℝ) + (nu : ℝ) * overhead + (sigma : ℝ)

/-- `Δ/footprint`, not `43/footprint`. -/
def clockRatio : ℝ := (Delta : ℝ) / footprint

/-- `((σ − χ) − 1/Δ)/(ν + σ + χ)`, not `(3 − 1/43)/23`. -/
def selfCoupling : ℝ :=
  (((sigma : ℝ) - (chi : ℝ)) - 1 / (Delta : ℝ)) /
    ((nu : ℝ) + (sigma : ℝ) + (chi : ℝ))

def scalarToll : ℝ := 2 * selfCoupling

/-- `ν − χ/(σ − χ) − α`, not `16 − 2/3 − α`. -/
def residual (α : ℝ) : ℝ :=
  (nu : ℝ) - (chi : ℝ) / ((sigma : ℝ) - (chi : ℝ)) - α

theorem overhead_eq : overhead = PMConstants.overhead := by
  rw [show overhead = 171 / 172 from PMSubstrate.E8Values.overhead_eq]
  rfl

theorem strongCoupling_eq (α : ℝ) :
    strongCoupling α = PMConstants.strongCoupling α := by
  unfold strongCoupling PMConstants.strongCoupling
  rw [overhead_eq, nu_eq, D_eq]
  norm_num

theorem footprint_eq : footprint = PMConstants.footprint := by
  unfold footprint PMConstants.footprint
  rw [overhead_eq, RM_eq, nu_eq, sigma_eq]
  norm_num

theorem clockRatio_eq : clockRatio = PMConstants.clockRatio := by
  unfold clockRatio PMConstants.clockRatio
  rw [footprint_eq, Delta_eq]
  norm_num

theorem selfCoupling_eq : selfCoupling = PMConstants.selfCoupling := by
  unfold selfCoupling PMConstants.selfCoupling
  rw [nu_eq, sigma_eq, chi_eq, Delta_eq]
  norm_num

theorem scalarToll_eq : scalarToll = PMConstants.scalarToll := by
  unfold scalarToll PMConstants.scalarToll
  rw [selfCoupling_eq]

theorem residual_eq (α : ℝ) : residual α = PMConstants.residual α := by
  unfold residual PMConstants.residual
  rw [nu_eq, sigma_eq, chi_eq]
  norm_num

end PMConstants.E8Values
