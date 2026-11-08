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

/-- Generic hierarchical path operator with diagonal entries `a,b,c`. -/
def HierarchicalOperator (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + a, -1, 0;
     -1, 37 / 16 + b, -21 / 16;
     0, -21 / 16, 21 / 16 + c]

/-- Characteristic polynomial of the generic hierarchical path operator. -/
theorem charpoly_eq (a b c x : ℝ) :
    (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - HierarchicalOperator a b c).det =
      x ^ 3 - ((8 * (a + b + c) + 37) / 8) * x ^ 2 +
        ((16 * a * b + 16 * a * c + 58 * a + 16 * b * c + 37 * b + 53 * c + 63) / 16) * x -
        ((16 * a * b * c + 21 * a * b + 37 * a * c + 21 * a + 16 * b * c + 21 * b + 21 * c) / 16) := by
  rw [Matrix.det_fin_three]
  simp [HierarchicalOperator]
  ring

theorem hierarchicalPathOperator_eq :
    hierarchicalPathOperator =
      HierarchicalOperator wallMassLowSq wallMassMidSq wallMassHighSq := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchicalPathOperator, HierarchicalOperator, pathOperator,
      Matrix.diagonal, wallMassLowSq, wallMassMidSq, wallMassHighSq]

end PMFlavor.HierarchicalPathOperator
