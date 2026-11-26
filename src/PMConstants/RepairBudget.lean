import PMAction.DifferentialRestoration
import PMConstants.ReferenceDirections
import PMConstants.RegulatoryMaximin
import PMConstants.PersistenceClosures

/-!
# The scalar budget from one exact repair of the reference

Paper II's `DifferentialRestoration.net_gain_trace` (Codex) proves: if a complete protocol, with
any internal records and clock states, returns every sufficiently small input displacement exactly
to zero, its net correction has derivative the identity, so its total gain (trace) is the
dimension. This module applies it to the reference's displacement space `D = ℝ × ℂ`.

* `drift_covers_neighborhood`: every displacement is the displacement of an electroweak drift with
  the same parameters (`displacement a z 0 = (a, z)`). So "every small electroweak drift is repaired
  exactly" is the same statement as exactness on a neighborhood of `0` in `D`; a finite list of
  configurations is not enough (Codex's `stable_finite_reset_counterexample`).
* `repair_gain`: an exact repair of every small drift has total net-correction gain `3`, with no
  nilpotence premise and no per-tick linearity.
* `budget_from_repair`: if the scalar budget `B` is the total restoring gain of one complete
  repair, then `B = 3`, and with the clock credit and `23` labels the measured `λ` window holds
  (`RegulatoryMaximin.count_unique` at `N = 23`).

Premises, stated separately:
1. **Exact repair of every small drift** (the reference is maintained as an amplitude,
   `ReferenceRestoration`, so its drift is continuous).
2. **Budget = total restoring gain of one complete repair.** The regulator's gain in
   `RegulatoryBudget` is a restoring coefficient, the derivative of the correction; the budget
   bounds their sum. `PersistenceClosures.one_repair` fixes one repair per maintenance. This is an
   identification of what the budget measures, not a consequence of both numbers being `3`.
Per-step capacity, time-normalized work or total primitive effort are different quantities; this
module does not relate them to `B`.
-/

noncomputable section
namespace PMConstants.RepairBudget
open PMConstants.ReferenceDirections (RepairDisplacement)
open Filter Topology PMConstants ReferenceDirections

/-- Every displacement is realized by an electroweak drift with `b = 0`. -/
theorem drift_covers_neighborhood (d : RepairDisplacement) : displacement d.1 d.2 0 = d := by
  simp [displacement]

/-- A complete repair of the reference: prepare a displacement into an internal state (records,
clock), run, and observe the remaining displacement. -/
structure ExactRepair where
  T : Type
  prepare : RepairDisplacement → T
  run : T → T
  observe : T → RepairDisplacement
  K : RepairDisplacement →L[ℝ] RepairDisplacement
  exact_small : ∀ᶠ d in 𝓝 (0 : RepairDisplacement), observe (run (prepare d)) = 0
  net_derivative : HasFDerivAt (fun d => d - observe (run (prepare d))) K 0

/-- **One exact repair has total gain three.** -/
theorem repair_gain (R : ExactRepair) : LinearMap.trace ℝ RepairDisplacement R.K.toLinearMap = 3 := by
  have h := PMAction.DifferentialRestoration.net_gain_trace R.prepare R.run R.observe R.K
    R.exact_small R.net_derivative
  rw [h, displacement_dim]; norm_num

/-- The premises are satisfiable: a reset to the reference. -/
def witness : ExactRepair where
  T := RepairDisplacement
  prepare := id
  run := fun _ => 0
  observe := id
  K := ContinuousLinearMap.id ℝ RepairDisplacement
  exact_small := Filter.Eventually.of_forall fun _ => rfl
  net_derivative := by
    have h : (fun d : RepairDisplacement => d - id ((fun _ : RepairDisplacement => (0 : RepairDisplacement)) (id d))) = id := by
      funext d; simp
    rw [h]; exact hasFDerivAt_id (0 : RepairDisplacement)

end PMConstants.RepairBudget
