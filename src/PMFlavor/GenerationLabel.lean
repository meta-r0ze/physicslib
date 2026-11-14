import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Root moves conserve the generation label; mixing needs a single-wall carrier move

A generation puts nontrivial `D₄` glue classes `b` and `c` (`b ≠ c`) on the two walls
(`PMConstants.Generations.three_pairs`); its label is the class it omits, which in the glue group
`G = Z₂ × Z₂` is `m = b + c` (the sum of two distinct nontrivial classes is the third).

`E₈` is glued from `D₄ ⊕ D₄` by pairing equal glue classes (`PMSubstrate.ChannelSymmetry`; every
gluing into an even unimodular lattice reduces to this by a triality in one sector). So a root of
`E₈` shifts both walls by the same class `a`, and a root of either `D₄` shifts neither.

* `root_move_conserves`: `(b + a) + (c + a) = b + c`. Every root move conserves the generation
  label. A flavour link built from root moves is diagonal in generation, and up- and down-type
  links built that way give no mixing.
* `single_wall_shift`: shifting one wall by `a` moves the label by `a`. Such a move is not an `E₈`
  vector; it is a minimal vector of one `D₄*` nontrivial class, a carrier.
* `transition_class`: going from generation `m` to `m'` takes the single-wall class `a = m + m'`,
  and for distinct nontrivial `m, m'` this is the third nontrivial class (`third_class`).

So all of the CKM/PMNS mixing comes from single-wall carrier exchange, and each pair of
generations mixes through its own class: three mixings, three classes. The class amplitudes, and
how the reference (which singles out one class) and chirality (which separates the other two)
break the triality `S₃` among them, are what determine the angles.

**The resulting pattern (reading, not yet derived).** Call the reference's class `v` (the
carriers use the vector class, `PMConstants.CarrierRepresentation`) and the other two `s`, `c`.
Two generations contain `v` (labels `s` and `c`); one does not (label `v`, walls `{s, c}`). The
two `v`-containing generations mix through `v` itself (`s + c = v`); each mixes with the
reference-free generation through `s` or `c`. If exchange through the reference's own class stays
inside the reference cell while exchange through `s` or `c` crosses the node (admittance `α`),
the reference-free generation is the weakly mixed one. The CKM forms follow that split:
`s₁₂ = π/(ν − χ)` carries no `α`, while `|V_cb| = (π + χ)/(α⁻¹ − Dπ)` and
`s₁₃ = 1/(χα⁻¹ + π)` are both of order `α`. The PMNS reactor angle `3α` fits it as well; the
`s`/`c` split is the weak current's parity violation (`ExchangeChirality`).
-/

namespace PMFlavor.GenerationLabel

/-- The glue group `D₄*/D₄`. -/
abbrev Glue := ZMod 2 × ZMod 2

/-- The generation label of a two-wall state: the class it omits. -/
def label (b c : Glue) : Glue := b + c

lemma add_self (a : Glue) : a + a = 0 := by
  ext <;> simp [CharTwo.add_self_eq_zero]

/-- **Root moves conserve the generation label.** -/
theorem root_move_conserves (b c a : Glue) : label (b + a) (c + a) = label b c := by
  unfold label
  rw [show b + a + (c + a) = b + c + (a + a) by abel, add_self, add_zero]

/-- **A single-wall shift moves the label by its class.** -/
theorem single_wall_shift (b c a : Glue) : label (b + a) c = label b c + a := by
  unfold label; abel

/-- **The class a transition needs.** -/
theorem transition_class (b c m' : Glue) :
    label (b + (label b c + m')) c = m' := by
  unfold label
  rw [show b + (b + c + m') + c = (b + b) + (c + c) + m' by abel, add_self, add_self]
  simp

/-- Two distinct nontrivial classes sum to the third. -/
theorem third_class : ∀ m m' : Glue, m ≠ 0 → m' ≠ 0 → m ≠ m' →
    m + m' ≠ 0 ∧ m + m' ≠ m ∧ m + m' ≠ m' := by
  decide

end PMFlavor.GenerationLabel
