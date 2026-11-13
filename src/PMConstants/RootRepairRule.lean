import PMConstants.ControllerIdentification
import PMAction.Machine.FactorRepair

/-!
# The typed repair lengths from the gauge factors

`TypedRepairWork.common_repair_cannot_match`: one common repair length for every carrier type
cannot give E8's mixing `clockRatio`. `target_budget_unique`: the least-cost typed repair that
does give it is unique, `(Q, u, d, L, e) = (2, 1, 1, 1, 1)` (`weakWitness`, cost `21`).

**Rule.** A gauge-active carrier needs one repair event per non-abelian factor it is charged under,
and at least one. A sterile carrier (`ν`, no gauge charge) raises no flag and needs none.

The rule was first found by asking what reproduces the witness. It is now derived from the factor
structure, without the mixing constraint:

* `weak_acts_on_sign`, `colour_acts_on_axis`: on the carriers `±2eᵢ`, read as the `(4, 2)` of
  `SU(4) × SU(2)` (`CarrierRepresentation`), the weak action reverses the sign (the doublet index)
  and keeps the axis, and a colour exchange permutes the colour axes and keeps the sign. Each is
  one generator of one factor: the identity on the `4` tensored with the `su(2)` Weyl reflection,
  and an `su(3)` root reflection tensored with the identity on the `2`.
* `PMAction.FactorRepair.repair_least`: a root event acts in one non-abelian factor (the roots of a
  product algebra are the disjoint union of the factors' roots), and the abelian phase, which has
  no roots, rides on any event's amplitude. Conservation then needs one event per displaced
  factor, and Economy takes exactly that many.
* `repairs_from_factors`: the rule is `max(#non-abelian factors, [Y ≠ 0])` with the derived
  hypercharges, type by type.
* `repairs_least`: so for a carrier displaced in the factors it is charged under, the least repair
  has exactly `repairs t` events.
* `rule_eq_witness`, `rule_mixing`: the rule gives `(2, 1, 1, 1, 1, 0)` and hence `clockRatio`,
  which is now a consequence rather than the constraint the rule was fitted to.
* `rule_least`: it costs no more than any positive typed repair that gives `clockRatio`.

* `electron_one_event`: the electron is a singlet of colour and weak, so any root event acts on it
  only through its phase; its repair is exactly one event (`PMAction.FactorRepair.singlet_least`).
  This is the "electron's maintenance is one repair" of `VevPremises`.

Premise: a disturbance displaces a carrier in the factors it is charged under, each undone by one
event of that factor.
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

/-- **Weak acts on the doublet index only**: it reverses every coordinate, so a carrier keeps its
axis and changes sign. -/
theorem weak_acts_on_sign :
    ∀ v : CarrierRepresentation.V, ∀ i,
      CarrierRepresentation.coord (CarrierActions.signExchange v) i =
        -CarrierRepresentation.coord v i := by
  decide +kernel

/-- **Colour acts on the axis only**: a colour exchange permutes the colour axes' coordinates. -/
theorem colour_acts_on_axis :
    ∀ a b : Fin 3, ∀ v : CarrierRepresentation.V, ∀ i,
      CarrierRepresentation.coord (CarrierActions.axisExchange a b v) i =
        CarrierRepresentation.coord v
          (Equiv.swap (CarrierActions.colourAxis a) (CarrierActions.colourAxis b) i) := by
  decide +kernel

/-- **The rule is one event per displaced factor**, with the derived hypercharges. -/
theorem repairs_from_factors (t : Ty) :
    repairs t = max ((if colourDim t = 3 then 1 else 0) + (if isoDim t = 2 then 1 else 0))
      (if hyper Hypercharge.standard t ≠ 0 then 1 else 0) := by
  cases t <;> norm_num [repairs, nonAbelian, colourDim, isoDim, hyper, Hypercharge.standard]

/-- **The least repair of a displaced carrier has `repairs t` events.** -/
theorem repairs_least {Gc Gw P : Type*} [Group Gc] [Group Gw] [CommGroup P]
    [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] (t : Ty) (g : Gc × Gw × P)
    (hc : g.1 ≠ 1 ↔ colourDim t = 3) (hw : g.2.1 ≠ 1 ↔ isoDim t = 2)
    (hp : g.2.2 ≠ 1 ↔ hyper Hypercharge.standard t ≠ 0) :
    IsLeast {n | ∃ L : List (Gc × Gw × P), (∀ e ∈ L, PMAction.FactorRepair.IsEvent e) ∧
      L.prod = g ∧ L.length = n} (repairs t) := by
  have h : PMAction.FactorRepair.need g = repairs t := by
    rw [repairs_from_factors t]
    unfold PMAction.FactorRepair.need PMAction.FactorRepair.displaced
    simp only [hc, hw, hp]
  rw [← h]
  exact PMAction.FactorRepair.repair_least g

/-- **The electron's repair is one event.** It is a singlet of colour and weak, so a root event
acts on it only through its phase: one event, carrying the phase, repairs it, and none does not. -/
theorem electron_one_event {Gc Gw P : Type*} [Group Gc] [Group Gw] [CommGroup P]
    (p : P) (hp : p ≠ 1) (r : Gc × Gw) (hr : r.1 = 1 ∨ r.2 = 1) :
    colourDim .e = 1 ∧ isoDim .e = 1 ∧ repairs .e = 1 ∧
      IsLeast {n | ∃ L : List (Gc × Gw × P), (∀ e ∈ L, PMAction.FactorRepair.IsEvent e) ∧
        (L.map fun e => e.2.2).prod = p ∧ L.length = n} 1 := by
  classical
  exact ⟨rfl, rfl, rfl, PMAction.FactorRepair.singlet_least p hp r hr⟩

end PMConstants.RootRepairRule
