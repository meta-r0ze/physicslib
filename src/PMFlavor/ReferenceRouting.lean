import PMAction.GenerationLabel

/-!
# Node routing from the reference's class

`TransferGraph.inCycle_iff` split the three generation transfers (one in-cycle, two node crossings)
with the protocols' lepton-axis rule applied to wire carriers, which the 2026-11 correction withdrew
(`ExchangeAxis` status). The wire supplies the split another way. `PMAction.ReferenceClassHop`: on
the reference's wall, a direct (Hamiltonian) exchange into or out of the reference's class would move
the reference out of its class, so the reference stays a stationary zero mode only if such
exchanges vanish there; they need a process that restores the reference (through its node). The
charged current acts on the reference's wall (`PMAction.ChiralityConvention.weak_acts_on_reference`).

A generation puts nontrivial classes on the two walls; a transfer to another generation is a
single-wall shift by the class `a` that changes its label (`PMAction.GenerationLabel.single_wall_shift`,
`transition_class`). On the reference's wall the shift takes the wall's class `f` to `f + a`.

* `avoids_reference_iff`: with `r` the reference's class, a nontrivial shift `f ↦ f + a` between
  nontrivial classes avoids `r` at both ends exactly when `a = r`.
* `direct_iff`: so the transfer by class `a` is direct on the reference's wall for every starting
  class exactly when `a = r`, and every other transfer touches the reference's class.

With `GenerationLabel`'s pairing (generations `m`, `m'` transfer through `m + m'`), the one direct
transfer joins the two generations that contain `r`, and both transfers of the generation labelled
`r` (the reference-free one) cross the node: the routing `TransferGraph` used, now from the
reference's stationarity instead of the axis rule. Inputs: the reference occupies one class (the
vector class, `PMAction.ReferenceClassHop`), and the charged current acts on the reference's wall.
How many legs a node crossing uses (`NodeAmplitude`) is separate.
-/

namespace PMFlavor.ReferenceRouting
open PMAction.GenerationLabel

/-- **A wall-class shift avoids the reference's class exactly when it is a shift by that class.** -/
theorem avoids_reference_iff : ∀ r f a : Glue, r ≠ 0 → f ≠ 0 → f + a ≠ 0 → a ≠ 0 →
    ((f ≠ r ∧ f + a ≠ r) ↔ a = r) := by
  decide

/-- A transfer by class `a` is direct on the reference's wall: from every nontrivial class it can
start at, neither end is the reference's class. -/
def Direct (r a : Glue) : Prop := ∀ f : Glue, f ≠ 0 → f + a ≠ 0 → f ≠ r ∧ f + a ≠ r

instance (r a : Glue) : Decidable (Direct r a) := by unfold Direct; infer_instance

/-- **Exactly the transfer through the reference's class is direct.** -/
theorem direct_iff : ∀ r a : Glue, r ≠ 0 → a ≠ 0 → (Direct r a ↔ a = r) := by
  decide

/-- The direct transfer joins the two generations that contain the reference's class: generations
`m ≠ m'` transfer through `m + m'`, and `m + m' = r` leaves `m, m'` the two classes other than `r`,
each of whose generations carries `r`. -/
theorem direct_pair : ∀ r m m' : Glue, r ≠ 0 → m ≠ 0 → m' ≠ 0 → m ≠ m' →
    (m + m' = r ↔ (m ≠ r ∧ m' ≠ r)) := by
  decide

end PMFlavor.ReferenceRouting
