import PMConstants.InterfaceWeightWindow

/-! **Geometric reading of the interface weight.**

The draft's geometric decomposition is

```
σ = 5 = 3 spatial directions + 2 boundary parameters.
```

The interface window independently selects effective weight `5`, so the active
response modes are exactly the spatial directions plus the `χ=2` boundary
parameters.  This is the geometric identification of the five-mode response, not a
fit to the window.
-/

noncomputable section
namespace PMConstants.InterfaceGeometry

open PMConstants

/-- Spatial directions `D−1`. -/
def spatialDirections : ℕ := PMSubstrate.E8Values.D - 1

/-- Boundary parameters `χ`. -/
def boundaryParameters : ℕ := PMSubstrate.E8Values.chi

/-- Active interface response modes. -/
def activeResponseModes : ℕ := spatialDirections + boundaryParameters

theorem spatialDirections_eq : spatialDirections = 3 := by
  norm_num [spatialDirections, PMSubstrate.E8Values.D_eq]

theorem boundaryParameters_eq : boundaryParameters = 2 := by
  norm_num [boundaryParameters, PMSubstrate.E8Values.chi_eq]

theorem activeResponseModes_eq : activeResponseModes = 5 := by
  norm_num [activeResponseModes, spatialDirections, boundaryParameters,
    PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.chi_eq]

/-- The active response modes are the interaction rank `σ`. -/
theorem activeResponseModes_eq_sigma :
    activeResponseModes = PMSubstrate.E8Values.sigma := by
  rw [activeResponseModes_eq, PMSubstrate.E8Values.sigma_eq]

/-- The geometrically identified five modes lie in the interface window. -/
theorem geometric_weight_in_window :
    0.0349 < InterfaceWeightWindow.deltaRWeight activeResponseModes ∧
      InterfaceWeightWindow.deltaRWeight activeResponseModes < 0.0353 := by
  rw [activeResponseModes_eq]
  exact InterfaceWeightWindow.weight_five_in_window

end PMConstants.InterfaceGeometry
