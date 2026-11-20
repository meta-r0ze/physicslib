import PMElementaryParticles.MuonRadiativeLog

/-!
# The leading-log contact coefficient is zero (not radiative stage 2)

This file records one fact: the leading-log coefficient of the muon's
charged-current contact is zero (`MuonRadiativeLog.leptonic_no_log` and
`retention_no_log`).  The toy `leadingLogKernel` below is a finite part plus
two supplied log terms multiplied by that same coefficient; it is
independent of those supplied scales because the coefficient is zero.

This is **not** radiative stage 2.  It does not assemble the vertex,
self-energy and real-emission diagrams, and it does not show that the
ultraviolet and infrared regulator logs cancel between them.  Radiative
stage 2 remains open in `REVIEW-AND-NEXT.md`.
-/

noncomputable section
namespace PMElementaryParticles.RadiativeStage2

open PMAction.ContactRunning
open PMElementaryParticles.MuonRadiativeLog

/-- The leading-log coefficient of the muon's charged-current contact. -/
def logCoefficient : ℝ := contactCoefficient 0 (-1) (-1) 0

theorem logCoefficient_eq_zero : logCoefficient = 0 := leptonic_no_log

/-- A leading-log toy kernel: finite part plus two supplied log terms with
zero contact coefficient.  This is not an assembled diagram kernel. -/
def leadingLogKernel (α uvLog irLog finite : ℝ) : ℝ :=
  finite + (2 * logCoefficient * (α / (4 * Real.pi))) * (uvLog + irLog)

/-- The toy leading-log kernel reduces to its finite part. -/
theorem leadingLogKernel_eq_finite (α uvLog irLog finite : ℝ) :
    leadingLogKernel α uvLog irLog finite = finite := by
  rw [leadingLogKernel, logCoefficient_eq_zero]
  ring

/-- The toy kernel is independent of the two supplied log scales. -/
theorem leadingLogKernel_independent_of_log_scales (α uvLog irLog finite : ℝ) :
    leadingLogKernel α uvLog irLog finite = leadingLogKernel α 0 0 finite := by
  rw [leadingLogKernel_eq_finite, leadingLogKernel_eq_finite]

/-- The leading-log rate factor is one for the toy kernel. -/
theorem leadingLogRateFactor (α uvLog irLog : ℝ) :
    leadingLogKernel α uvLog irLog 1 = 1 :=
  leadingLogKernel_eq_finite α uvLog irLog 1

end PMElementaryParticles.RadiativeStage2
