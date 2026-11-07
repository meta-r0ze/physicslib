import PMConstants.ControllerLedger

/-! **Experimental/candidate module.**

# Physical controller identification

The physical controller is identified with the baseline least-cost typed-repair
candidate: all five gauge-active repairs have length one, the neutral repair is
unconstrained and set to zero.  This is a model identification, not a derivation
of the typed-repair ledger from bare persistence.
-/

noncomputable section
namespace PMConstants.ControllerIdentification

open PMConstants.ControllerLedger PMConstants.TypedRepairWork

/-- Baseline least-cost controller. -/
def physicalController : ControllerCandidate := ⟨1, 1, 1, 1, 1, 0⟩

theorem physicalController_admissible : BaselineAdmissible physicalController := by
  norm_num [physicalController, BaselineAdmissible, Positive]

theorem physicalController_cost : controllerCost physicalController = 15 := by
  norm_num [physicalController, controllerCost, activeBudget]

/-- It is a least-cost admissible controller. -/
theorem physicalController_least (r : ControllerCandidate)
    (hr : BaselineAdmissible r) :
    controllerCost physicalController ≤ controllerCost r := by
  rw [physicalController_cost]
  exact baseline_bound r hr

/-- At cost 15 the gauge-active baseline components are unique.  The neutral
repair length is unconstrained by the active budget. -/
theorem physicalController_components (r : ControllerCandidate)
    (hr : BaselineAdmissible r) (hc : controllerCost r = 15) :
    r.q = 1 ∧ r.u = 1 ∧ r.d = 1 ∧ r.l = 1 ∧ r.e = 1 :=
  baseline_unique r hr (by simpa [controllerCost] using hc)

/-- Gauge-active controller: the target-mixing least-cost repair. -/
def gaugeController : ControllerCandidate := weakWitness

theorem gaugeController_cost : controllerCost gaugeController = 21 := by
  norm_num [gaugeController, controllerCost, activeBudget, weakWitness]

theorem gaugeController_admissible : TargetAdmissible gaugeController := by
  norm_num [gaugeController, TargetAdmissible, Positive, weakWitness]

/-- The gauge controller reproduces the clock mixing ratio. -/
theorem gaugeController_mixing :
    PMConstants.GaugeReadoutWeights.mixing (weights gaugeController) =
      PMConstants.clockRatio := by
  rw [target_iff _ gaugeController_admissible.1]
  norm_num [gaugeController, weakWitness]

end PMConstants.ControllerIdentification
