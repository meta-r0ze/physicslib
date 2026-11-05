import PMConstants.Partition
import PMSubstrate.Impedance

/-!
# The Cabibbo deficit is the per-direction reference exclusion

Paper III's reference-frame overhead is `η = 171/172`: exactly one of the `172`
frame cells is reserved for the reference (`ReferenceFrames.optimal_172_overhead`,
`Partition.overhead`). The frame is `D·Δ = 4·43 = 172`, four rows of `43` phase
addresses (`RequirementRows`).

The **per-direction** reference exclusion is therefore

    (1 − η)/D = 1/(D·172) = 1/688.

So the Cabibbo dressing `q² = 687/688` is not an independent numerical choice: it
is the reference-frame deficit shared over the `D` lattice directions. What remains
Paper IV's application claim is that the CKM first row inherits this deficit.
-/

noncomputable section
namespace PMConstants.FlavourDressing
open PMSubstrate

/-- The two invariant expressions for the denominator `688`. -/
theorem denominator_invariants :
    (baseline.sectorChannels : ℝ) * (baseline.period : ℝ) = 688 ∧
      (baseline.dimension : ℝ) * (baseline.resolution : ℝ) = 688 := by
  norm_num [PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

/-- **The Cabibbo dressing deficit is one reference exclusion per direction.** -/
theorem cabibbo_deficit_per_direction :
    1 - (1 - overhead) / (baseline.dimension : ℝ) = 687 / 688 := by
  norm_num [overhead, PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

/-- The same deficit written with the frame resolution `R_M = D·Δ = 172`. -/
theorem cabibbo_deficit_frame :
    1 - 1 / ((baseline.dimension : ℝ) * (baseline.resolution : ℝ)) = 687 / 688 := by
  norm_num [PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

end PMConstants.FlavourDressing
