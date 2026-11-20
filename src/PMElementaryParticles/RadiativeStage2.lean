import PMElementaryParticles.MuonRadiativeLog

/-!
# Radiative stage 2: the assembled kernel and regulator-log cancellation

The one-loop contact dressing is the sum of the finite kernel and the
ultraviolet and infrared regulator logs.  For muon decay the charged-current
contact has zero log coefficient (`MuonRadiativeLog.leptonic_no_log` and
`retention_no_log`).  Consequently the assembled kernel is independent of both
regulator scales.  This is the stage-2 statement; the Feynman-parameter
integrals that fix the finite part are stage 3 and are not claimed here.
-/

noncomputable section
namespace PMElementaryParticles.RadiativeStage2

open PMAction.ContactRunning
open PMElementaryParticles.MuonRadiativeLog

/-- The leading-log coefficient of the muon's charged-current contact. -/
def logCoefficient : ℝ := contactCoefficient 0 (-1) (-1) 0

theorem logCoefficient_eq_zero : logCoefficient = 0 := leptonic_no_log

/-- The assembled one-loop kernel: a finite part plus the ultraviolet and
infrared regulator logs, both with the same contact coefficient. -/
def assembledKernel (α uvLog irLog finite : ℝ) : ℝ :=
  finite + (2 * logCoefficient * (α / (4 * Real.pi))) * (uvLog + irLog)

/-- Stage 2: both regulator logs cancel. -/
theorem regulator_logs_cancel (α uvLog irLog finite : ℝ) :
    assembledKernel α uvLog irLog finite = finite := by
  rw [assembledKernel, logCoefficient_eq_zero]
  ring

/-- The assembled kernel has zero derivative in either regulator scale. -/
theorem independent_of_regulators (α uvLog irLog finite : ℝ) :
    assembledKernel α uvLog irLog finite = assembledKernel α 0 0 finite := by
  rw [regulator_logs_cancel, regulator_logs_cancel]

/-- The assembled rate factor is one at leading log, so the surviving
regulator dependence is the finite kernel alone. -/
theorem assembled_rate_factor (α uvLog irLog : ℝ) :
    assembledKernel α uvLog irLog 1 = 1 :=
  regulator_logs_cancel α uvLog irLog 1

end PMElementaryParticles.RadiativeStage2
