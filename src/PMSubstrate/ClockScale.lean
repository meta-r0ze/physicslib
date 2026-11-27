import PMSubstrate.E8Values
import Mathlib.Tactic

/-!
# Root updates and physical time are different units

Delta counts root updates. It does not supply a duration in electron time
units. The one named conversion premise is in SCOPE: an admitted physical
root update has a supplied positive duration kappa in electron time units.
No theorem in this module selects kappa. The legacy unit-tick candidate
sets kappa = 1; the existing atoms/e8p value 43 is its whole-period duration,
not the duration of one receiver update. The legacy numerical values stay.

The context relation between a reversal rate and a natural-unit mass is NOT
a PM premise here. The conditional equations below expose its consequences.
One reversal per Delta updates and unit electron rate require kappa=1/Delta.
The legacy kappa=1 instead gives rate 1/Delta. Unit rate at kappa=1 requires
Delta reversals per Delta updates, conflicting with the strict Margin ceiling.
-/
noncomputable section
namespace PMSubstrate.ClockScale

/-- SCOPE's tick-to-time input; no value is selected by the substrate clock theorem. -/
structure TickDuration where
  electronUnits : ℝ
  positive : 0 < electronUnits

def periodTime (clock : TickDuration) : ℝ := (E8Values.Delta : ℝ)*clock.electronUnits

/-- Existing comparison convention, not a derived physical calibration. -/
def legacyUnitTick : TickDuration := ⟨1,by norm_num⟩

def seconds (clock : TickDuration) (electronSecond : ℝ) : ℝ := clock.electronUnits*electronSecond

/-- Unit conversion for an observed reversal count. No physical mass is defined here. -/
def perElectronTime (clock : TickDuration) (reversals ticks : ℝ) : ℝ :=
  reversals / (ticks*clock.electronUnits)

theorem legacy_period : periodTime legacyUnitTick = 43 := by
  norm_num [periodTime,legacyUnitTick,E8Values.Delta,E8Values.Delta_eq]

theorem one_per_period_legacy : perElectronTime legacyUnitTick 1 E8Values.Delta = 1/43 := by
  norm_num [perElectronTime,legacyUnitTick,E8Values.Delta,E8Values.Delta_eq]

/-- Conditional on the context rate relation and electron rate 1; not a calibration proof. -/
theorem one_per_period_unit_rate (clock : TickDuration)
    (h : perElectronTime clock 1 E8Values.Delta = 1) : clock.electronUnits = 1/43 := by
  have hp := clock.positive
  change (1 : ℝ)/(43*clock.electronUnits) = 1 at h
  have hd : (43 : ℝ)*clock.electronUnits ≠ 0 := by positivity
  have he := (div_eq_iff hd).mp h
  linarith

theorem legacy_unit_rate_saturates (r : ℝ)
    (h : perElectronTime legacyUnitTick r E8Values.Delta = 1) : r = 43 := by
  norm_num [perElectronTime,legacyUnitTick,E8Values.Delta,E8Values.Delta_eq] at h
  linarith

theorem legacy_unit_rate_excludes_margin (r : ℝ) (hm : r ≤ 42) :
    perElectronTime legacyUnitTick r E8Values.Delta ≠ 1 := by
  intro h
  have := legacy_unit_rate_saturates r h
  linarith

end PMSubstrate.ClockScale
