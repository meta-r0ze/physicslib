import PMConstants.CarrierActions
import PMAction.SignFlip

/-!
# The weak refresh keeps the label

`PMConstants.CarrierActions.weak` is the sign exchange on the reference's sector and the identity on
the other (`refresh_is_sign`, `refresh_fixes_other`).

* `refresh_keeps_class`: the sign exchange maps vector-class carriers to vector-class carriers
  (`negative_valid`); no carrier changes glue class.
* `refresh_same_axis`: it keeps every carrier's axis; by `CarrierActions.same_axis_iff` the sign is
  the only such move, so the sign is the doublet index and the refresh exchanges doublet partners.
* `refresh_keeps_label`: as a glue move the flip `x ↦ −x` is in the trivial class
  (`PMAction.SignFlip`), so on every generation state it keeps the label.

So the weak refresh changes the protocol (doublet position: up ↔ down, `ν ↔ e`) and never the
label. In particular it does not supply `EventTransfer.J`'s in-cycle entry `κ₀` (labels `2 → 1`),
which needs a single-wall shift by the nontrivial vector class (`GenerationCurrent`). Where that
change comes from, if anywhere at the event level, is PMFlavor REVIEW item 0.
-/

namespace PMFlavor.RefreshLabel
open PMConstants.CarrierActions PMConstants.CarrierRepresentation PMAction.GenerationSector

/-- **The refresh is the sign exchange on the reference's sector.** -/
theorem refresh_is_sign (v : V) : weak (Sum.inl v) = Sum.inl (signExchange v) := rfl

/-- **The other sector is fixed.** -/
theorem refresh_fixes_other (v : V) : weak (Sum.inr v) = Sum.inr v := rfl

/-- **No carrier changes class**: the image of a vector-class carrier is vector-class. -/
theorem refresh_keeps_class (v : V) : PMAction.CarrierEvents.valid 0 (signExchange v).1 :=
  negative_valid v

/-- **The refresh keeps every carrier's axis**: it is the doublet exchange. -/
theorem refresh_same_axis (v : V) :
    ∀ i, (coord v i ≠ 0 ↔ coord (signExchange v) i ≠ 0) :=
  (same_axis_iff v (signExchange v)).2 (Or.inr rfl)

/-- **The refresh keeps the label**: a sign flip is a trivial-class glue move. -/
theorem refresh_keeps_label : ∀ b c : Glue, IsGen b c →
    PMAction.GenerationLabel.label (-b) c = PMAction.GenerationLabel.label b c :=
  fun b c h => (PMAction.SignFlip.flip_keeps_state b c h).2

/-- **It is not a label change**: no nontrivial single-wall shift gives the flipped class. -/
theorem refresh_not_label_change : ∀ b a : Glue, a ≠ 0 → b + a ≠ -b :=
  PMAction.SignFlip.flip_not_label_change

end PMFlavor.RefreshLabel
