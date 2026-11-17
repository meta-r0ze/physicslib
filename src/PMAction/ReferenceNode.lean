import PMAction.KronReduction
import PMAction.GenerationLabel

/-!
# The reference-restoring node as a star: `k/K = α/n`

`ReferenceClassHop`: on the reference's wall, direct exchange into or out of the reference's class
vanishes, so the two light generations' insertions need a process that restores the reference.
Model that process as a conserving node `R` (a Laplacian vertex, as in `KronReduction`), the
reference's maintenance, joined by one leg of admittance `α` to each class mode it can restore from
or to. Closure gives every crossing one price (`PMConstants.HandoffAdmittance.closure_one_price`), so
the legs are equal. The classes also keep their direct link `K` (`s ↔ c`, the exchange through the
reference's class, which `ReferenceClassHop` allows).

* `star_pair`: eliminating a node with `n` equal legs `α` couples each pair of its classes by `α/n`
  (the Schur complement `−α·α/(nα)`).
* `star_three`: with legs to all three classes of the wall (the reference's own class, to which it is
  restored, and the two it can be displaced into), the restored couplings are `α/3`, and the direct
  pair gets `K + α/3`.
* `two_leg_case`: with legs only to the two classes of one crossing, the series value `α/2`
  (`NodeAmplitude.node_series`).

So `k/K = α/3` if the node joins all three classes, `α/2` if it joins only the crossing's two.

**Which legs.** A leg is an exchange between the node and a carrier mode that is there. On the
reference's wall a generation state occupies one class, and the reference occupies its own class `r`;
a single-wall move takes the occupied class `f` to `f + a`. So during a move the node can reach the
classes `{f, f + a, r}`:
* `restoring_two_classes`: when the move touches `r` (the moves `ReferenceClassHop` sends through the
  node), that set has exactly two classes;
* `direct_three_classes`: the direct move (`a = r`) involves all three, and needs no node.
With legs only to occupied modes, every restoring crossing has two legs, and `restoring_series`:
`k/K = α/2`, for both light insertions (one enters `r`, one leaves it) and both node transfer edges.
This is `NodeAmplitude`'s value, now with its two legs counted from the occupied modes; it matches
the charge-weight test and the `α/2` scale of `|V_ub|` (`PMFlavor.CKM`: `1/(2α⁻¹ + π)`). Premise:
the node has legs only to occupied carrier modes, with one price (Closure).

The star model is symmetric in the classes, so it gives both light insertions the same `k` (which the
charge-weight test prefers, PMFlavor REVIEW "Leg count") and both node transfer edges the same size:
a `|V_cb| ≠ |V_ub|` asymmetry has to come from what breaks `s ↔ c` (the charged current's wall,
`ExchangeChirality`), not from the node. Which legs the node has is the remaining premise.
-/

namespace PMAction.ReferenceNode

/-- **A node with `n` equal legs couples each pair of its classes by `α/n`.** -/
theorem star_pair (α : ℝ) (n : ℕ) (_hα : 0 < α) (hn : 0 < n) :
    0 - (-α) * (-α) / ((n : ℝ) * α) = -(α / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

/-- **Three legs: the restored couplings are `α/3`, and the direct pair `K + α/3`.** -/
theorem star_three (K α : ℝ) (hα : 0 < α) :
    (0 - (-α) * (-α) / (3 * α) = -(α / 3)) ∧ (-K - (-α) * (-α) / (3 * α) = -(K + α / 3)) := by
  have h : α ≠ 0 := hα.ne'
  constructor <;> field_simp <;> ring

/-- **Two legs: the series value `α/2`.** -/
theorem two_leg_case (α : ℝ) (hα : 0 < α) : 0 - (-α) * (-α) / (2 * α) = -(α / 2) := by
  have h := star_pair α 2 hα (by norm_num)
  simpa using h

open PMAction.GenerationLabel in
/-- **A move that touches the reference's class involves exactly two classes.** -/
theorem restoring_two_classes : ∀ r f a : Glue, r ≠ 0 → f ≠ 0 → f + a ≠ 0 → a ≠ 0 →
    (f = r ∨ f + a = r) → ({f, f + a, r} : Finset Glue).card = 2 := by
  decide

open PMAction.GenerationLabel in
/-- **The direct move involves all three classes.** -/
theorem direct_three_classes : ∀ r f : Glue, r ≠ 0 → f ≠ 0 → f + r ≠ 0 →
    ({f, f + r, r} : Finset Glue).card = 3 := by
  decide

/-- **So a restoring crossing is the two-leg series, `k/K = α/2`.** -/
theorem restoring_series (α : ℝ) (hα : 0 < α) :
    0 - (-α) * (-α) / (((2 : ℕ) : ℝ) * α) = -(α / 2) := by
  simpa using star_pair α 2 hα (by norm_num)

end PMAction.ReferenceNode
