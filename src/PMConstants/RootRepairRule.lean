import PMConstants.ControllerIdentification

/-! **Experimental/candidate module.**

# A root-event rule for the typed repair lengths

`TypedRepairWork.common_repair_cannot_match`: one common repair length for every carrier type
cannot give E8's mixing `clockRatio`. `target_budget_unique`: the least-cost typed repair that
does give it is unique, `(Q, u, d, L, e) = (2, 1, 1, 1, 1)` (`weakWitness`, cost `21`).

This module states a rule that produces that vector from the carriers' representation content
(`RequirementTable.colourDim`, `isoDim`), without the mixing constraint:

**Rule.** A gauge-active carrier needs one repair event per non-abelian factor it is charged under,
and at least one. A sterile carrier (`ν`, no gauge charge) raises no flag and needs none.

Reading. Primitive events are root hops. The roots of a product of simple factors are the
disjoint union of each factor's roots, so one root event acts in one factor: a carrier with
colour and weak holonomies (`Q`) needs two events. The hypercharge phase is not a root direction;
it multiplies whichever event occurs, so it adds no event, except that a carrier with only
hypercharge (`e`) still needs one event to be repaired at all.

* `rule_eq_witness`: the rule gives `(2, 1, 1, 1, 1, 0)`, the witness.
* `rule_mixing`: so it gives `clockRatio`.
* `rule_least`: it costs no more than any positive typed repair that gives `clockRatio`.

Status: the rule was found by asking what reproduces the witness, so it explains the selected
controller rather than predicting a new number (the same status as the `f_K` routing reading).
What it adds is a reason in root geometry for why only `Q` costs two. Not derived: that a
repair is a sequence of root events, one per factor; and that the abelian phase adds none.
-/

noncomputable section
namespace PMConstants.RootRepairRule
open RequirementTable TypedRepairWork ControllerLedger GaugeReadoutWeights

/-- Number of non-abelian factors (colour, weak) a carrier type is charged under. -/
def nonAbelian (t : Ty) : ℕ :=
  (if 1 < colourDim t then 1 else 0) + (if 1 < isoDim t then 1 else 0)

/-- **The rule.** One event per non-abelian factor, at least one for a gauge-active carrier,
none for the sterile carrier. -/
def repairs : Ty → ℕ
  | .n => 0
  | t => max 1 (nonAbelian t)

/-- The rule's repair vector. -/
def ruleRepairs : Repairs :=
  ⟨repairs .Q, repairs .u, repairs .d, repairs .L, repairs .e, repairs .n⟩

/-- **The rule gives the witness** `(2, 1, 1, 1, 1, 0)`. -/
theorem rule_eq_witness : ruleRepairs = weakWitness := rfl

/-- **The rule gives E8's mixing.** -/
theorem rule_mixing : mixing (weights ruleRepairs) = PMConstants.clockRatio := by
  rw [rule_eq_witness, target_iff _ (by norm_num [Positive, weakWitness])]
  norm_num [weakWitness]

/-- **The rule is least-cost** among positive typed repairs that give E8's mixing. -/
theorem rule_least (r : Repairs) (hr : Positive r)
    (h : mixing (weights r) = PMConstants.clockRatio) :
    activeBudget ruleRepairs ≤ activeBudget r := by
  rw [rule_eq_witness]
  have h21 : activeBudget weakWitness = 21 := by norm_num [activeBudget, weakWitness]
  rw [h21]
  exact target_budget_bound r hr ((target_iff r hr).mp h)

end PMConstants.RootRepairRule
