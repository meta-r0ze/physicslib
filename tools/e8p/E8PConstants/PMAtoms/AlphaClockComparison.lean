import PMAtoms.AlphaFinite
import PMAtoms.ClockHierarchy
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Capacity clocks vs nested clocks

The current alpha attempt uses

`attempt = workload / Δ`,

i.e. a capacity convention: more parallel channels give a shorter effective
period `Δ / workload`.

A nested gated-clock convention would instead use

`period = workload · Δ`.

This module proves the two conventions and their ratio, so the modeling choice
is explicit rather than hidden.
-/

noncomputable section
namespace E8PConstants.AlphaClockComparison
open PMAtoms PMElementaryParticles PMConstants

/-- Capacity-convention period. -/
def capacityPeriod (workload : ℝ) : ℝ := e8Tick / workload

/-- Nested/gated-convention period. -/
def gatedPeriod (workload : ℝ) : ℝ := workload * e8Tick

theorem alphaFlux_eq_inv_tick : alphaFlux = 1 / e8Tick := by
  unfold alphaFlux e8Tick
  norm_num [PMSubstrate.E8Values.Delta, PMSubstrate.baseline]

/-- The current alpha attempt is the inverse capacity period. -/
theorem alphaAttempt_eq_inv_capacityPeriod {p : Nuclide}
    (hZ : 0 < p.Z) (hN : 0 < p.N) :
    alphaAttempt p = 1 / capacityPeriod (alphaWorkload p) := by
  have hw : 0 < alphaWorkload p := alphaWorkload_pos hZ hN
  unfold alphaAttempt capacityPeriod
  rw [alphaFlux_eq_inv_tick]
  field_simp [hw.ne']

/-- A nested attempt is the inverse gated period. -/
def alphaNestedAttempt (p : Nuclide) : ℝ :=
  1 / gatedPeriod (alphaWorkload p)

theorem alphaNestedAttempt_eq {p : Nuclide} :
    alphaNestedAttempt p = 1 / (alphaWorkload p * e8Tick) := rfl

/-- Capacity and nested conventions differ by the square of the workload. -/
theorem capacity_vs_nested_ratio {workload : ℝ} (hw : 0 < workload) :
    (1 / capacityPeriod workload) / (1 / gatedPeriod workload) = workload ^ 2 := by
  have ht : (0 : ℝ) < e8Tick := by rw [e8Tick_eq]; norm_num
  unfold capacityPeriod gatedPeriod
  field_simp [hw.ne', ht.ne']

theorem alpha_capacity_vs_nested_ratio {p : Nuclide}
    (hZ : 0 < p.Z) (hN : 0 < p.N) :
    alphaAttempt p / alphaNestedAttempt p = (alphaWorkload p) ^ 2 := by
  rw [alphaAttempt_eq_inv_capacityPeriod hZ hN]
  unfold alphaNestedAttempt
  exact capacity_vs_nested_ratio (alphaWorkload_pos hZ hN)

/-- Concrete check of the example hierarchy `10 · 2 · 6 · 43`. -/
theorem nestedPeriod_10_2_6 : nestedPeriod [10, 2, 6] = 5160 := by
  norm_num [nestedPeriod, e8Tick_eq]

end AlphaClockComparison
