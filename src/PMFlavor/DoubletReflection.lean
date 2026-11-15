import PMFlavor.ExchangeAxis

/-!
# The doublet sign is not a geometric source of the up/down split

Can the wire's geometry tell up from down? `PMConstants.CarrierRepresentation`: in the right sector
the up and down quarks are the positive and negative colour carriers `±2eᵢ` (`i ≠ 0`), the doublet
sign; the reference is on axis `0`.

Reflect one colour axis, `flip i` (`x_i ↦ −x_i`):
* `flip_keeps_reference_axis`: it fixes axis `0`, so it fixes the reference's axis.
* `flip_vector`: it maps the vector class to itself, and `flip_doublet`: on a colour carrier of
  axis `i` it reverses the doublet sign (`positive`): up ↔ down.
* `flip_spinor`, `flip_cospinor`: it exchanges the spinor and cospinor classes, the `s ↔ c` swap
  that the mass formula already treats as a symmetry (`LightSplit.light_split`,
  `ExchangeChirality.swap_with_exchange`).

So any amplitude built from the `D₄` carrier geometry and the reference's axis, and invariant
under the `s ↔ c` swap, is the same for up and down. Any up/down difference is not geometric: it
needs a charge that tells the doublet sign apart (the right-sector hypercharge `Y = B − L + 2T₃`,
`CarrierRepresentation.charges_from_carriers`) or a breaking of the swap, that is, protocol content.
-/

namespace PMFlavor.DoubletReflection
open PMAction.CarrierEvents PMConstants.CarrierRepresentation

/-- Reflect axis `i`. -/
def flip (i : Fin 4) (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun j => if j = i then -x j else x j

theorem flip_keeps_reference_axis (i : Fin 4) (hi : i ≠ 0) (x : Fin 4 → ℤ) :
    flip i x 0 = x 0 := by
  simp [flip, Ne.symm hi]

theorem flip_vector : ∀ i : Fin 4, ∀ v : Carrier 0, ∃ v' : Carrier 0,
    vector v' = flip i (vector v) := by
  decide +kernel

theorem flip_spinor : ∀ i : Fin 4, ∀ d : Carrier 1, ∃ d' : Carrier 2,
    vector d' = flip i (vector d) := by
  decide +kernel

theorem flip_cospinor : ∀ i : Fin 4, ∀ d : Carrier 2, ∃ d' : Carrier 1,
    vector d' = flip i (vector d) := by
  decide +kernel

theorem flip_doublet : ∀ i : Fin 4, ∀ v v' : V, vector v' = flip i (vector v) →
    coord v i ≠ 0 → positive v' = !positive v := by
  decide +kernel

end PMFlavor.DoubletReflection
