import PMAtoms.Invariants

/-!
# Atom-specific E8 closure identities

These identities belong to the atom ladder, not to the substrate record.
They are proved here from the canonical substrate invariants.
-/

namespace PMAtoms

/-- `Δ + σ = (σ−χ)ν = 48`. -/
theorem delta_add_sigma : Δ + σ = (σ - χ) * ν := by
  decide

/-- Proton closure `2(Δ−χ) = 82`. -/
theorem proton_closure : 2 * (Δ - χ) = 82 := by
  decide

/-- Neutron closure `(σ−χ)(Δ−1) = 126`. -/
theorem neutron_closure : (σ - χ) * (Δ - 1) = 126 := by
  decide

/-- Deformed proton closure `2(Δ+σ) = 96`. -/
theorem deformed_proton_closure : 2 * (Δ + σ) = 96 := by
  decide

/-- Upper neutron closure `D(Δ+σ−χ) = 184`. -/
theorem upper_neutron_closure : D * (Δ + σ - χ) = 184 := by
  decide

/-- Deformation denominator `(D+χ)(σ−χ)ν = 288`. -/
theorem deformation_denominator : (D + χ) * (σ - χ) * ν = 288 := by
  decide


/-- Deformed neutron closure `(σ−χ)Δ + (ν+σ+χ) = 152`. -/
def deformedNeutronShell : Nat := (σ - χ) * Δ + (ν + σ + χ)

theorem deformedNeutronShell_eq : deformedNeutronShell = 152 := by
  norm_num [deformedNeutronShell, σ, χ, Δ, ν, PMSubstrate.baseline]

end PMAtoms
