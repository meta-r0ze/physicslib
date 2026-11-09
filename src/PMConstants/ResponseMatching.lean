import PMConstants.EventStiffness
import PMConstants.ReferenceStiffness

/-!
# The electromagnetic matching as a substrate response equation (S5)

The substrate *computes* the electromagnetic response. The quadratic part of its gauge action is
the Yang–Mills Hessian (`PMAction.GaugeFluctuation.quad_eq_hess`: `quad a = ½ Σ_ν ⟨a_ν, (K a)_ν⟩`,
`K = −D² + 2[F,·]`), and its infrared (zero-momentum) value is the event-priced gauge stiffness
`gsq` — computed from the substrate's events by `EventStiffness.coupling_from_events`
(`gsq(c0·toll·m·W) = 1/(toll·m·W)`).

The *matching* (that this response reproduces the substrate's net impedance `Z_geo`) is **not an
additional hypothesis**: the constants layer *defines* the fine-structure constant as the
substrate's own per-cycle admittance `α := causalCoupling = 1/Z_geo`, so `α⁻¹ = Z_geo` is a theorem
and the impedance form `4π/g²(0) = Z_geo` is the rationalized-units normalization `g² = 4πα`
applied to it (`matching_frontier_iff_admittance`). Equivalently, the matching is exactly the
electric calibration the tree already assumes (`matching_frontier_iff_calibration`, the premise of
`EventStiffness.calibration`). What remains physical is the single identification `α = κ` — that
the fine-structure constant is the substrate's admittance — stated once; the response-and-impedance
algebra around it is proved.
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

/-- **The matching frontier.** The electromagnetic matching as a substrate equation: the
reciprocal of the substrate's infrared gauge response reproduces its net impedance `Z_geo`. Every
ingredient is proved — the response (`irResponse_eq`, `quad_eq_hess`) and the impedance (the
six-term index) — so this is a *rewriting* of a single identification, not a new hypothesis
(see `matching_frontier_iff_admittance`, `matching_frontier_iff_calibration`). -/
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

/-- The substrate's per-cycle admittance `κ = 1/Z_geo`. The constants layer *defines* the
fine-structure constant as this (`PMConstants.CertifiedConstants.α := PMSubstrate.causalCoupling`,
with `1/α = geometricIndex` proved in `JointConstants`/`ScaleResponse`). So the matching
equation `α⁻¹ = Z_geo` is a theorem, not an extra physical input. -/
theorem admittance_eq_inv_index :
    PMSubstrate.causalCoupling = 1 / PMSubstrate.geometricIndex := rfl

theorem inv_admittance_eq_index :
    (PMSubstrate.causalCoupling)⁻¹ = PMSubstrate.geometricIndex := by
  rw [PMSubstrate.causalCoupling, one_div, inv_inv]

/-- **The matching is the Maxwell normalization of the substrate's own admittance, not an extra
hypothesis.** The impedance form `4π/g²(0) = Z_geo` is exactly `g²(0) = 4π·κ` — the definition of
`α` in rationalized natural units (`α = g²/4π`) applied to the substrate's admittance `κ = α`.
(`PhysicalBridge.response_leaves_matching_free` shows positivity cannot fix the coefficient `4π`;
the convention `g² = 4πα` does.) -/
theorem matching_frontier_iff_admittance (toll : ℝ) (m : ℕ) (W : ℝ) :
    matching_frontier toll m W ↔
      irResponse toll m W = 4 * Real.pi * PMSubstrate.causalCoupling := by
  rw [admittance_eq_inv_index, matching_frontier, irResponse]
  constructor <;> intro h <;> rw [h] <;> ring

/-- **The matching frontier is the electric calibration.** At the system footprint `W = N_sys`,
`matching_frontier` is *exactly* the premise of `EventStiffness.calibration`
(`g²(footprint) = 4πα`), whose conclusion pins the event product `toll·m`. So the "matching" is
the tree's electric calibration restated in impedance form — the response reproduces `Z_geo`
because the calibration sets it to `4π·α = 4π/Z_geo`, with `α` *defined* as the substrate's
admittance. -/
theorem matching_frontier_iff_calibration (toll : ℝ) (m : ℕ) :
    matching_frontier toll m footprint ↔
      GaugeStiffness.gsq (EventStiffness.c0 toll m * footprint) =
        4 * Real.pi * PMSubstrate.causalCoupling := by
  rw [matching_frontier_iff_admittance]
  rfl

/-- Given the electric calibration the matching frontier holds: the calibration is the only
input, and the impedance form is its rewriting. -/
theorem matching_frontier_of_calibration (toll : ℝ) (m : ℕ)
    (hcal : GaugeStiffness.gsq (EventStiffness.c0 toll m * footprint) =
        4 * Real.pi * PMSubstrate.causalCoupling) :
    matching_frontier toll m footprint :=
  (matching_frontier_iff_calibration toll m).mpr hcal

/-- **The matching workload is the substrate's own electric ledger.** The electric sector refreshes
exactly its required resources, so its refresh count is `ledger reqSU2 + ledger reqY = footprint`
(`GaugeLedgers.footprint_from_rule`). So `matching_frontier toll m footprint` is the matching at a
*substrate-fixed* workload, not a chosen one. -/
theorem footprint_eq_electric_ledger :
    footprint =
      GaugeLedgers.ledger GaugeLedgers.reqSU2 + GaugeLedgers.ledger GaugeLedgers.reqY :=
  GaugeLedgers.footprint_from_rule.symm

/-- The matching **determines** the substrate's event product `toll·m·W`: `4π/g²(0) = Z_geo`
holds exactly when `toll·m·W = Z_geo/(4π)`. So the matching is not a free physical hypothesis — it
is the condition that the substrate's event pricing is normalized to its own admittance. -/
theorem matching_frontier_iff_event_product (toll : ℝ) (m : ℕ) (W : ℝ)
    (h : toll * m * W ≠ 0) :
    matching_frontier toll m W ↔ toll * m * W = PMSubstrate.geometricIndex / (4 * Real.pi) := by
  have hZ : PMSubstrate.geometricIndex ≠ 0 := by
    have := PMSubstrate.geometricIndex_gt_one; linarith
  have h4 : (4 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [matching_frontier, irResponse_eq, div_eq_div_iff h hZ, one_mul, eq_div_iff h4]
  constructor
  · intro hh; rw [hh]; ring
  · intro hh; rw [← hh]; ring

end PMConstants.ResponseMatching
