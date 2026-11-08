import PMConstants.InterfaceWeightWindow
import PMSubstrate.DerivedParameters
import PMSubstrate.PersistenceMaximin

/-! **Geometric interface modes from PMSubstrate.**

The five-mode count is already owned by `PMSubstrate.Derived.configDim`:

```
configDim D q = (D − q) + 2 = 3 spatial + 2 boundary = σ.
```

This module only connects that existing count to the interface window.  The equal
weight of the five modes is the maximin law of `PMSubstrate.PersistenceMaximin`,
not a new assumption.
-/

noncomputable section
namespace PMConstants.InterfaceGeometry

open PMConstants

/-- The substrate's configuration dimension at `D=4`, one time direction. -/
abbrev activeResponseModes : ℕ :=
  PMSubstrate.Derived.configDim PMSubstrate.E8Values.D 1

theorem activeResponseModes_eq : activeResponseModes = 5 := by
  unfold activeResponseModes PMSubstrate.Derived.configDim
  rw [PMSubstrate.E8Values.D_eq]

/-- The configuration dimension is the interaction rank `σ`. -/
theorem activeResponseModes_eq_sigma :
    activeResponseModes = PMSubstrate.E8Values.sigma := by
  rw [activeResponseModes_eq, PMSubstrate.E8Values.sigma_eq]

/-- The maximin persistence law is uniform on five modes. -/
theorem uniform_five_weights (p : Fin 5 → ℝ)
    (hp : PMSubstrate.PersistenceMaximin.Maximin p) (i : Fin 5) :
    p i = 1 / 5 := by
  rw [PMSubstrate.PersistenceMaximin.maximin_iff] at hp
  rw [hp i]
  norm_num

/-- The geometrically identified five modes lie in the interface window. -/
theorem geometric_weight_in_window :
    0.0349 < InterfaceWeightWindow.deltaRWeight activeResponseModes ∧
      InterfaceWeightWindow.deltaRWeight activeResponseModes < 0.0353 := by
  rw [activeResponseModes_eq]
  exact InterfaceWeightWindow.weight_five_in_window

end PMConstants.InterfaceGeometry
