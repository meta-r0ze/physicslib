import PMConstants.GenerationWalls
import PMFlavor.ExchangeAxis

/-!
# What separates the two node-crossing mixings: the wall a class sits on

`ExchangeAxis` derived which generation pair mixes inside the cycle (through the reference's
class `v`) and left the other two pairs, through `s` and `c`, indistinguishable by the axis
test. This module places them on the two walls of `PMConstants.GenerationWalls`, where generation
`g` carries class `g + 1` on one wall and `g − 1` on the other (`side`), and the inter-wall hop
`hop ⊗ Y` is the generation dynamics.

* `hop_class`: generations `g`, `g'` share exactly one class, the third one; a carrier of that class
  hopping between walls is what moves a mode from `g` to `g'`. This is the class `m + m'` of
  `GenerationLabel.transition_class`, so the two pictures agree on which class carries each
  mixing.
* `free_generation_split`: the reference-free generation (`g = v`) has its two classes on
  **opposite walls**. So the two node-crossing mixings hop classes that sit on opposite walls of
  that generation: one on the reference's (weak) wall, one on the other.
* `swap_reverses_side`: the class swap fixing `v` (`x ↦ 2v − x`, the generation-level action of
  Paper I's `flip`, `ChannelSymmetry.flip_class`) reverses every wall assignment.
  `swap_not_symmetry`: it is not a symmetry of the incidence on its own;
  `swap_with_exchange`: composed with the wall exchange it is.

The wall exchange is the parity that flips the wall chirality
(`PMAction.ChiralityConvention.exchange_flips_chirality`), and the charged current couples to one
wall only (`WallChiralCurrent.selected_iff`, the reference's wall). So the `s ↔ c` symmetry that
the axis test sees is exactly the parity combined with the class swap; **the `s`/`c` split is the
weak current's parity violation**, not a new input. Which spinor class sits on the weak wall in the
reference-free generation is the incidence orientation (`GenerationWalls.balanced_classification`),
the same binary convention that names "left".

For leptons this agrees with `GenerationBreaking.pmns_no_shared_state`: the residual `Z₂` must be
broken there too, and the source is the same weak current. The near-maximal `θ₂₃` is then a small
breaking, not an unbroken symmetry. How large the breaking is in each sector, and the `α` cost of
the node passage, are not derived here.
-/

namespace PMFlavor.ExchangeChirality
open PMConstants.GenerationWalls

theorem hop_class : ∀ g g' : Fin 3, g ≠ g' →
    ∃! c : Fin 3, c ≠ g ∧ c ≠ g' := by
  simp only [ExistsUnique]
  decide

theorem free_generation_split : ∀ v : Fin 3, side v (v + 1) = true ∧ side v (v - 1) = false := by
  decide

/-- The class swap fixing `v`. -/
def swap (v x : Fin 3) : Fin 3 := 2 * v - x

theorem swap_fixes : ∀ v, swap v v = v := by decide

theorem swap_involutive : ∀ v x, swap v (swap v x) = x := by decide

theorem swap_reverses_side : ∀ v g c : Fin 3, g ≠ c → side (swap v g) (swap v c) = !side g c := by
  decide

theorem swap_not_symmetry : ∀ v : Fin 3, ¬ ∀ g c : Fin 3, g ≠ c →
    side (swap v g) (swap v c) = side g c := by decide

theorem swap_with_exchange : ∀ v g c : Fin 3, g ≠ c →
    !side (swap v g) (swap v c) = side g c := by decide

end PMFlavor.ExchangeChirality
