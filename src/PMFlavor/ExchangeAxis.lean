import PMConstants.CarrierRepresentation
import PMFlavor.GenerationLabel

/-!
# Which exchange classes avoid the reference axis

`GenerationLabel`: root moves conserve the generation label, so generations mix only by a
single-wall carrier exchange, and generations `m`, `m'` mix through the class `m + m'`. This
module asks which classes can supply that exchange inside the reference-maintaining cycle.

`LeptonAxisRestriction` derived that no admissible cycle event may touch the reference
(lepton) axis `0`: a type-changing event cannot be undone by the type-preserving gauge repair.
A single-wall exchange displaces a wall carrier by a minimal vector of the exchange class
(`PMAction.CarrierEvents.Carrier`), so the same test applies to the displacement.

* `vector_free`: `6` of the `8` vector-class displacements (`±2eᵢ`, `i ≠ 0`) have no axis-`0`
  component; `vector_touch`: the other `2` lie on it.
* `spinor_touch`, `cospinor_touch`: **every** spinor and conjugate-spinor displacement
  `(±1, ±1, ±1, ±1)` has axis-`0` component `±1`.
* `moves_onto_axis`: so a spinor or conjugate-spinor exchange takes any colour-axis state
  (axis-`0` component `0`) to one with nonzero axis-`0` component; it changes the channel type,
  exactly the event `LeptonAxisRestriction` excludes from the cycle.
* `one_pair_through`: for a fixed nonzero class `v` exactly one unordered pair of generations
  mixes through `v`.

So, with `v` the reference's (vector) class: of the three generation pairs, exactly one (the two
generations containing `v`, labels `s` and `c`) has in-cycle exchange channels. The other two
pairs mix only through `s` or `c`, whose exchange necessarily touches the reference axis and so
cannot be a gauge-repairable cycle event: it has to pass through the reference node. This is now
a derived split, not a reading: in-cycle exchange counts are `(6, 0, 0)` for `(v, s, c)`.

What it does not fix. The axis test treats `s` and `c` identically (each displacement has
`|axis-0 component| = 1`, and `flip` keeps axis `0` while swapping them,
`GenerationBreaking.flip_keeps_axis`), so the `s`/`c` split (`|V_ub|` vs `|V_cb|`) must come from
an orientation (chirality) input, and the leptons' near-maximal `θ₂₃` is what an unbroken `s ↔ c`
looks like. That the node passage costs exactly the admittance `α` per crossing, and the in-cycle
amplitude through `v`, are not derived here.
-/

namespace PMFlavor.ExchangeAxis
open PMAction.CarrierEvents

theorem vector_free :
    (Finset.univ.filter fun d : Carrier 0 => vector d 0 = 0).card = 6 := by decide +kernel

theorem vector_touch :
    (Finset.univ.filter fun d : Carrier 0 => vector d 0 ≠ 0).card = 2 := by decide +kernel

theorem spinor_touch : ∀ d : Carrier 1, vector d 0 = 1 ∨ vector d 0 = -1 := by decide +kernel

theorem cospinor_touch : ∀ d : Carrier 2, vector d 0 = 1 ∨ vector d 0 = -1 := by decide +kernel

theorem spinor_ne (c : Fin 3) (hc : c ≠ 0) (d : Carrier c) : vector d 0 ≠ 0 := by
  fin_cases c
  · exact absurd rfl hc
  · rcases spinor_touch d with h | h <;> simp [h]
  · rcases cospinor_touch d with h | h <;> simp [h]

theorem moves_onto_axis (c : Fin 3) (hc : c ≠ 0) (d : Carrier c) (x : Fin 4 → ℤ) (hx : x 0 = 0) :
    (x + vector d) 0 ≠ 0 := by
  simpa [hx] using spinor_ne c hc d

open GenerationLabel in
theorem one_pair_through : ∀ v : Glue, v ≠ 0 →
    (Finset.univ.filter fun p : Glue × Glue =>
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.1 + p.2 = v).card = 2 := by
  decide

end PMFlavor.ExchangeAxis
