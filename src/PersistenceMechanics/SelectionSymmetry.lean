import Mathlib.Basic.Real.Basic

/-!
# Symmetry and selection

A general shape for the papers' open "model choices", independent of E8. A cost
functional can only select points it fixes: if a cost is invariant under a
transformation `τ` and some point is the *unique* least-cost point, that point is
`τ`-fixed. Contrapositively, a moved point has a distinct tied point, so a cost
whose minimizer is moved by `τ` has no unique minimizer.

Consequences for a persistence-by-cost argument:

* a **discrete** symmetry with a uniqueness-forcing (generic or strictly convex)
  cost resolves a choice — e.g. the two D₄ sectors (`PMConstants.SectorExchange`),
  or the uniform law (`LawSelection.uniform_law`);
* a **continuous** symmetry always ties and leaves the choice to a symmetry-breaking
  input — e.g. the CP-sign phase conjugation (`PMFlavor.ReferenceSelection`,
  `PMFlavor.ReferenceFlavour.conjugate_cost_tie`).

So "is this input derivable?" reduces to "is the relevant symmetry discrete *and*
does the cost force a unique minimizer?".
-/

namespace PersistenceMechanics.SelectionSymmetry

/-- **Selection by a symmetric cost can only pick symmetric points.** If `τ` preserves the
cost and `u` is the unique least-cost point, then `τ u = u`. -/
theorem unique_minimizer_fixed {U : Type*} (cost : U → ℝ) (τ : U → U)
    (hcost : ∀ u, cost (τ u) = cost u) (u : U)
    (hmin : ∀ v, cost u ≤ cost v) (huniq : ∀ v, (∀ w, cost v ≤ cost w) → v = u) :
    τ u = u :=
  huniq (τ u) (fun w => by rw [hcost u]; exact hmin w)

/-- **A moved point is tied.** If the cost is `τ`-invariant and `τ x ≠ x`, then there is a
point distinct from `x` with the same cost. So a symmetric cost cannot single out a
non-fixed point, and a continuous symmetry (whose orbit of `x` is nontrivial) forces a tie. -/
theorem exists_tied_of_moved {U : Type*} (cost : U → ℝ) (τ : U → U) (x : U)
    (hcost : ∀ u, cost (τ u) = cost u) (hmove : τ x ≠ x) :
    ∃ v, v ≠ x ∧ cost v = cost x :=
  ⟨τ x, hmove, hcost x⟩

end PersistenceMechanics.SelectionSymmetry
