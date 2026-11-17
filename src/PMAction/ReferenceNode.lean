import PMAction.KronReduction

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

So `k/K = α/3` if the node joins all three classes, `α/2` if it joins only the crossing's two. The
star model is symmetric in the classes, so it gives both light insertions the same `k` (which the
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

end PMAction.ReferenceNode
