import PMConstants.ReferenceMasses
import PMConstants.SharedReference

/-!
# Economy places the references; unbroken colour picks the lepton doublet

`SharedReference` takes two premises: distinct reference types occupy distinct reserved cells, and
the weak and hypercharge refreshes both read the reserved reference. Both follow from Economy once
the reserved cell is priced.

**Pricing.** The single reserved cell is already paid for by the frame overhead (`η = 171/172`). A
sector whose refresh can read it (positive response to the reserved type) needs no further
reference; any other sector needs a payload reference, costing `η > 0`.

* `extra_cost`: the added reference cost of a reserved type `t` is `η · (3 - #served t)`.
* `reads_reserved`: between reading the reserved cell (added cost `0`) and a payload reference
  (`η > 0`), the reserved cell is the unique cheapest read; so whenever `t` serves weak and
  hypercharge, both read the reserved reference. This is the second premise, given this pricing.
* `economy_unconstrained`: minimizing the added cost over all types selects `Q`, which serves all
  three sectors.
* `colour_unbroken_iff`: a type with zero colour response is `L`, `e` or `ν`. A coloured reserved
  type is moved by colour (`ReferenceStabilizer.quark_reference_breaks_colour`) and would break it.
* `economy_selects_lepton`: among colour-preserving types, the added cost is least exactly for `L`.
  So `L` follows from Economy plus unbroken colour, without the W mass; the W mass
  (`SharedReference.reference_selected`) is then an independent check, and also excludes `Q`.

**One cell, one type.** `cell_inj_of_content`: if each reserved cell holds one carrier state, whose
type is a function of the cell, then the cell map is injective on types. This is the first premise.
-/

noncomputable section
namespace PMConstants.ReferenceEconomy
open PMConstants GaugeReadoutWeights RequirementTable ReferenceCharge

def ind (x : ℝ) : ℕ := if 0 < x then 1 else 0

def servedCount : Ty → ℕ
  | .Q => 3 | .u => 2 | .d => 2 | .L => 2 | .e => 1 | .n => 0

/-- The table counts the sectors (weak, hypercharge, colour) with positive response. -/
theorem served_correct (t : Ty) :
    servedCount t = ind (weakIndex (ref t)) + ind (hyperIndex (ref t)) + ind (colourIndex (ref t)) := by
  cases t <;> norm_num [servedCount, ind, weakIndex, hyperIndex, colourIndex, ref]

/-- Added reference cost of a reserved type: one payload reference per unserved sector. -/
def extraCost (t : Ty) : ℝ := overhead * (3 - servedCount t)

theorem overhead_pos : 0 < overhead := by norm_num [overhead]

/-- The added cost of a served sector's reference read: `0` for the reserved cell (already paid by
the frame overhead), `η` for a payload reference. -/
def readCost (useReserved : Bool) : ℝ := if useReserved then 0 else overhead

/-- **A served sector's cheapest read is the reserved cell, uniquely.** -/
theorem reads_reserved :
    (∀ b, readCost true ≤ readCost b) ∧ ∀ b, readCost b = readCost true → b = true := by
  have h := overhead_pos
  refine ⟨fun b => ?_, fun b hb => ?_⟩ <;> cases b <;> simp_all [readCost]
  linarith

theorem economy_unconstrained (t : Ty) : extraCost .Q ≤ extraCost t ∧
    (extraCost t = extraCost .Q ↔ t = .Q) := by
  have h := overhead_pos
  have h' := h.ne'
  cases t <;> refine ⟨?_, ?_⟩ <;> norm_num [extraCost, servedCount] <;> positivity

theorem colour_unbroken_iff (t : Ty) : colourIndex (ref t) = 0 ↔ t = .L ∨ t = .e ∨ t = .n := by
  cases t <;> norm_num [colourIndex, ref]

/-- **Economy plus unbroken colour selects the lepton doublet.** -/
theorem economy_selects_lepton (t : Ty) (ht : colourIndex (ref t) = 0) :
    extraCost .L ≤ extraCost t ∧ (extraCost t = extraCost .L ↔ t = .L) := by
  have h := overhead_pos
  have h' := h.ne'
  rcases (colour_unbroken_iff t).mp ht with rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;>
    norm_num [extraCost, servedCount] <;> first | positivity | linarith

/-- **One cell, one type.** -/
theorem cell_inj_of_content (content : Fin 172 → Ty) (cell : Ty → Fin 172)
    (h : ∀ t, content (cell t) = t) : Function.Injective cell := by
  intro a b hab
  rw [← h a, ← h b, hab]

end PMConstants.ReferenceEconomy
