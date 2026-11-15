import PMFlavor.CKMDressing
import PMFlavor.FlavourInvariants
import PMConstants.FlavourDressing
import Mathlib.Tactic

/-!
# The Cabibbo dressing constant is a derived invariant expression

Upstream `PMConstants.FlavourDressing` shows the number is the reference-frame deficit carried by
the spatial outlets: with overhead `η = 171/172` and `D = 4`, `1 − (1−η)/(D − 1) = 515/516`.
The outlets are the three channels of the minimal dilation (`DressingChannels`), and the loss, a
registered transfer, puts no weight on the time axis (`DressingEvent`). An earlier version used the
uniform four-axis share `1 − (1−η)/D = 687/688`, which needs the time comparison to fire.

* `q2_eq_spatial_reference`, `q2_eq_frame_deficit` — the number is `1 − (1−η)/(D − 1)`, hence
  also `1 − 1/((D − 1)·R_M)` with `R_M = D·Δ = 172`.
* `spatial_denominator`, `deficit_eq` — the first-row deficit `1 − q²` is exactly
  `1/((D − 1)·D·Δ) = 1/516`.
* `q2_pos`, `q2_lt_one` — the dressing keeps the amplitude in `(0,1)`, so the dressed matrix is a
  genuine contraction.

It does **not** justify *why the CKM first row inherits* the reference deficit; that is the
remaining physical claim about the anomaly (see `E8PConstants.FlavourPulls.first_row_deficit_test`).
-/

noncomputable section
namespace PMFlavor.CabibboDressing
open PMSubstrate

/-- **`q2` is the reference deficit over the spatial directions.** This is the upstream
`PMConstants.FlavourDressing.cabibbo_deficit_spatial` expression. -/
theorem q2_eq_spatial_reference :
    CKMDressing.q2 = 1 - (1 - PMConstants.overhead) /
      ((PMSubstrate.baseline.dimension : ℝ) - 1) := by
  rw [PMConstants.FlavourDressing.cabibbo_deficit_spatial]
  unfold CKMDressing.q2
  norm_num

/-- The same deficit written with the frame resolution `R_M = D·Δ = 172`. -/
theorem q2_eq_frame_deficit :
    CKMDressing.q2 = 1 - 1 / (((PMSubstrate.baseline.dimension : ℝ) - 1) *
      (PMSubstrate.baseline.resolution : ℝ)) := by
  rw [PMConstants.FlavourDressing.cabibbo_deficit_frame]
  unfold CKMDressing.q2
  norm_num

/-- **The denominator `516` is `(D − 1)·R_M`.** -/
theorem spatial_denominator :
    ((PMSubstrate.baseline.dimension : ℝ) - 1) * (PMSubstrate.baseline.resolution : ℝ) = 516 :=
  PMConstants.FlavourDressing.spatial_denominator

/-- **The first-row deficit is `1/((D − 1)·R_M)`.** -/
theorem deficit_eq :
    1 - CKMDressing.q2 = 1 / (((PMSubstrate.baseline.dimension : ℝ) - 1) *
      (PMSubstrate.baseline.resolution : ℝ)) := by
  rw [q2_eq_frame_deficit]; ring

/-- The dressing keeps the amplitude in `(0,1)`: it is a genuine contraction. -/
theorem q2_pos : 0 < CKMDressing.q2 := by
  unfold CKMDressing.q2; norm_num
theorem q2_lt_one : CKMDressing.q2 < 1 := by
  unfold CKMDressing.q2; norm_num

/-- The dressed `|V_ud| = q · c₁₂c₁₃`, where `q² = 515/516`. -/
noncomputable def vudDressed : ℝ :=
  Real.sqrt CKMDressing.q2 * (CKM.c12 * CKM.c13)

/-- Certified enclosure of the dressed `|V_ud|`. -/
theorem vudDressed_bounds :
    (0.97354 : ℝ) < vudDressed ∧ vudDressed < 0.97357 := by
  have hq1 : (0.99903 : ℝ) < Real.sqrt CKMDressing.q2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [CKMDressing.q2]
  have hq2 : Real.sqrt CKMDressing.q2 < (0.99904 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [CKMDressing.q2]
  have hv := CKM.vud_bounds
  unfold vudDressed
  constructor <;> nlinarith [hq1, hq2, hv.1, hv.2]

end PMFlavor.CabibboDressing
