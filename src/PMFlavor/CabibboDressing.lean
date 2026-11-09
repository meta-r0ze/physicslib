import PMFlavor.CKMDressing
import PMFlavor.FlavourInvariants
import PMConstants.FlavourDressing
import Mathlib.Tactic

/-!
# The Cabibbo dressing constant is a derived invariant expression

Upstream `PMConstants.FlavourDressing` shows the number is the reference-frame
deficit shared over the lattice directions: with overhead `η = 171/172` and
`D = 4`, `1 − (1−η)/D = 687/688`. `q2_eq_per_direction_reference` below connects
`CKMDressing.q2` to that expression. The physical claim that the CKM first row
inherits the per-direction reference deficit remains the model step.

The original arithmetic observation was that the dressing turns exact CKM
unitarity into a `1 − 1/688` first-row sum, i.e. the claimed resolution of the
Cabibbo Angle Anomaly. The **number itself is not independent** — it is exactly

    q² = 1 − 1/(ν · Δ),

where `ν = 16` (`FlavourInvariants.nu`, derived in Paper I) and `Δ = 43` is the
forced clock period (`PMSubstrate.Impedance.baseline.period`, `parameters_forced`).
`ν · Δ = 688`, so `687/688 = 1 − 1/688` was the invariant expression all along,
written out.

**What this fixes and what it does not.**
* `q2_eq_per_direction_reference`, `q2_eq_frame_deficit` — the number is the
  per-direction reference exclusion `1 − (1−η)/D` from PMConstants, and hence also
  `1 − 1/(D·R_M)` with `R_M = D·Δ = 172`.
* `q2_eq_invariants` — the dressing amplitude squared is `1 − 1/(ν Δ)`, not a free
  literal; the denominator `688` is `ν·Δ` (`invariant_denominator`).
* `deficit_eq` — the first-row deficit `1 − q²` is exactly `1/(ν Δ)`.
* `q2_pos`, `q2_lt_one` — the dressing keeps the amplitude in `(0,1)`, so the
  dressed matrix is a genuine contraction.

It does **not** justify *why the CKM first row inherits* the per-direction
reference deficit; that is the remaining physical claim about the anomaly (see
`E8PConstants.FlavourPulls.first_row_deficit_test`). The arithmetic input is now the upstream
reference-frame deficit, not an independent fitted literal.
-/

noncomputable section
namespace PMFlavor.CabibboDressing
open PMSubstrate

/-- The forced clock period `Δ = 43` (Paper I `parameters_forced`). -/
def clock : ℕ := baseline.period

theorem clock_eq : clock = 43 := by decide

/-- **`q2` is the per-direction reference deficit.** This is the upstream
`PMConstants.FlavourDressing.cabibbo_deficit_per_direction` expression. -/
theorem q2_eq_per_direction_reference :
    CKMDressing.q2 = 1 - (1 - PMConstants.overhead) /
      (PMSubstrate.baseline.dimension : ℝ) := by
  rw [PMConstants.FlavourDressing.cabibbo_deficit_per_direction]
  unfold CKMDressing.q2
  norm_num

/-- The same deficit written with the frame resolution `R_M = D·Δ = 172`. -/
theorem q2_eq_frame_deficit :
    CKMDressing.q2 = 1 - 1 / ((PMSubstrate.baseline.dimension : ℝ) *
      (PMSubstrate.baseline.resolution : ℝ)) := by
  rw [PMConstants.FlavourDressing.cabibbo_deficit_frame]
  unfold CKMDressing.q2
  norm_num

/-- **The dressing amplitude squared is an invariant expression.** -/
theorem q2_eq_invariants :
    CKMDressing.q2 = 1 - 1 / ((FlavourInvariants.nu : ℝ) * (clock : ℝ)) := by
  have hnu : FlavourInvariants.nu = 16 := FlavourInvariants.nu_eq
  have hc : clock = 43 := clock_eq
  unfold CKMDressing.q2
  rw [hnu, hc]
  norm_num

/-- **The denominator `688` is `ν · Δ`.** -/
theorem invariant_denominator :
    (FlavourInvariants.nu : ℝ) * (clock : ℝ) = 688 := by
  have hnu : FlavourInvariants.nu = 16 := FlavourInvariants.nu_eq
  have hc : clock = 43 := clock_eq
  rw [hnu, hc]; norm_num

/-- **The first-row deficit is `1/(ν Δ)`.** -/
theorem deficit_eq :
    1 - CKMDressing.q2 = 1 / ((FlavourInvariants.nu : ℝ) * (clock : ℝ)) := by
  rw [q2_eq_invariants]; ring

/-- The dressing keeps the amplitude in `(0,1)`: it is a genuine contraction. -/
theorem q2_pos : 0 < CKMDressing.q2 := by
  unfold CKMDressing.q2; norm_num
theorem q2_lt_one : CKMDressing.q2 < 1 := by
  unfold CKMDressing.q2; norm_num

/-- The dressed `|V_ud| = q · c₁₂c₁₃`, where `q² = 687/688`. -/
noncomputable def vudDressed : ℝ :=
  Real.sqrt CKMDressing.q2 * (CKM.c12 * CKM.c13)

/-- Certified enclosure of the dressed `|V_ud|`. -/
theorem vudDressed_bounds :
    (0.97377 : ℝ) < vudDressed ∧ vudDressed < 0.97380 := by
  have hq1 : (0.99927 : ℝ) < Real.sqrt CKMDressing.q2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [CKMDressing.q2]
  have hq2 : Real.sqrt CKMDressing.q2 < (0.99928 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [CKMDressing.q2]
  have hv := CKM.vud_bounds
  unfold vudDressed
  constructor <;> nlinarith [hq1, hq2, hv.1, hv.2]

end PMFlavor.CabibboDressing
