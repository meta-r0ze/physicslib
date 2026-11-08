import PMFlavor.PathOperator
import PMAction.WallDispersion

/-! **Experimental/candidate module.**

# Hierarchical path operator

The diagonal mass-squared term uses the two-wall masses at

```
δ = χ = 2,  y = σ = 5
```

and the middle entry `χ² = 4`:

```
D = diag(massSqM χ σ, χ², massSqP χ σ).
```

No entry is fitted to CKM/PMNS.
-/

noncomputable section
namespace PMFlavor.HierarchicalPathOperator

open PMFlavor.PathOperator

/-- Light two-wall mass squared at `δ=χ`, `y=σ`. -/
def wallMassLowSq : ℝ := PMAction.WallDispersion.massSqM 2 5

/-- Middle mass squared: `χ²`. -/
def wallMassMidSq : ℝ := 4

/-- Heavy two-wall mass squared at `δ=χ`, `y=σ`. -/
def wallMassHighSq : ℝ := PMAction.WallDispersion.massSqP 2 5

theorem wallMassMidSq_eq_chi_sq : wallMassMidSq = (2 : ℝ) ^ 2 := by
  norm_num [wallMassMidSq]

/-- Path operator plus the hierarchical wall-mass diagonal. -/
def hierarchicalPathOperator : Matrix (Fin 3) (Fin 3) ℝ :=
  pathOperator + Matrix.diagonal ![wallMassLowSq, wallMassMidSq, wallMassHighSq]

end PMFlavor.HierarchicalPathOperator
