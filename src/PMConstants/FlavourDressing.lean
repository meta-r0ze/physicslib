import PMConstants.Partition
import PMSubstrate.Impedance

/-!
# The Cabibbo deficit is the reference exclusion carried by the spatial outlets

Paper III's reference-frame overhead is `η = 171/172`: exactly one of the `172`
frame cells is reserved for the reference (`ReferenceFrames.optimal_172_overhead`,
`Partition.overhead`). The frame is `D·Δ = 4·43 = 172`, four rows of `43` phase
addresses (`RequirementRows`).

The dressing loss leaves the CKM block through outlet channels, and a registered loss puts no
weight on the reference's time axis (`PMFlavor.DressingEvent`, the event principle of `VevEvent`).
So the exclusion is shared over the `D − 1` spatial directions:

    (1 − η)/(D − 1) = 1/(3·172) = 1/516,   q² = 515/516.

The uniform four-axis share `(1 − η)/D = 1/688` (`per_direction_share`) would need the time
comparison to fire. What remains Paper IV's application claim is that the CKM first row inherits
this deficit.
-/

noncomputable section
namespace PMConstants.FlavourDressing
open PMSubstrate

/-- The denominator `516 = (D − 1)·R_M`. -/
theorem spatial_denominator :
    ((baseline.dimension : ℝ) - 1) * (baseline.resolution : ℝ) = 516 := by
  norm_num [PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

/-- **The Cabibbo dressing deficit is the reference exclusion over the spatial directions.** -/
theorem cabibbo_deficit_spatial :
    1 - (1 - overhead) / ((baseline.dimension : ℝ) - 1) = 515 / 516 := by
  norm_num [overhead, PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

/-- The same deficit written with the frame resolution `R_M = D·Δ = 172`. -/
theorem cabibbo_deficit_frame :
    1 - 1 / (((baseline.dimension : ℝ) - 1) * (baseline.resolution : ℝ)) = 515 / 516 := by
  norm_num [PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

/-- The uniform four-axis share, which needs weight on the time axis. -/
theorem per_direction_share :
    1 - (1 - overhead) / (baseline.dimension : ℝ) = 687 / 688 := by
  norm_num [overhead, PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

end PMConstants.FlavourDressing
