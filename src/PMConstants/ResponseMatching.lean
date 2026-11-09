import PMConstants.EventStiffness
import PMConstants.ReferenceStiffness

/-!
# The electromagnetic matching as a substrate response equation (S5)

The substrate *computes* the electromagnetic response. The quadratic part of its gauge action is
the Yang–Mills Hessian (`PMAction.GaugeFluctuation.quad_eq_hess`: `quad a = ½ Σ_ν ⟨a_ν, (K a)_ν⟩`,
`K = −D² + 2[F,·]`), and its infrared (zero-momentum) value is the event-priced gauge stiffness
`gsq` — computed from the substrate's events by `EventStiffness.coupling_from_events`
(`gsq(c0·toll·m·W) = 1/(toll·m·W)`).

What is **not** yet derived is the *matching*: that this response reproduces the substrate's net
impedance `Z_geo`. This module names that single identification (`matching_frontier`) as a Lean
proposition, so the S5 frontier is a checked object rather than prose — exactly the step PM-1 calls
out as future work ("derive the matching condition by computing the substrate's coupling to a
background `U(1)` field and its quadratic response").
-/

noncomputable section
namespace PMConstants.ResponseMatching
open PMConstants

/-- The substrate's **infrared gauge response**: the event-priced stiffness `gsq` on the
event-count `c0·toll·m·W`. This is the zero-momentum value of the gauge action's quadratic part. -/
def irResponse (toll : ℝ) (m : ℕ) (W : ℝ) : ℝ :=
  GaugeStiffness.gsq (EventStiffness.c0 toll m * W)

/-- **The response is computed**: the event-priced stiffness is `1/(toll·m·W)`
(`EventStiffness.coupling_from_events`). So no free normalization sits in the response itself. -/
theorem irResponse_eq (toll : ℝ) (m : ℕ) (W : ℝ) :
    irResponse toll m W = 1 / (toll * (m : ℝ) * W) :=
  EventStiffness.coupling_from_events toll m W

/-- **The S5 frontier (open).** The electromagnetic matching as a substrate equation: the
reciprocal of the substrate's infrared gauge response reproduces its net impedance `Z_geo`. Every
ingredient is proved — the response (`irResponse_eq`, `quad_eq_hess`) and the impedance (the
six-term index) — the open content is this identification. Named here as the target. -/
def matching_frontier (toll : ℝ) (m : ℕ) (W : ℝ) : Prop :=
  irResponse toll m W = 4 * Real.pi / PMSubstrate.geometricIndex

/-- The frontier in the impedance form `4π/g² = Z_geo` (`PMSubstrate.PhysicalBridge.electromagnetic_matching`):
the two forms are the same statement. -/
theorem matching_frontier_iff (toll : ℝ) (m : ℕ) (W : ℝ)
    (hg : irResponse toll m W ≠ 0) :
    matching_frontier toll m W ↔
      (4 * Real.pi / irResponse toll m W = PMSubstrate.geometricIndex) := by
  have hZ : PMSubstrate.geometricIndex ≠ 0 := by
    have := PMSubstrate.geometricIndex_gt_one; linarith
  unfold matching_frontier
  rw [eq_div_iff hZ, div_eq_iff hg]
  constructor
  · intro h; rw [← h]; ring
  · intro h; rw [h]; ring

end PMConstants.ResponseMatching
