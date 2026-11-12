import Mathlib.Tactic

/-!
# The minimal persistent cube

An `n × n × n` cubic block persists as a volume only if some vertex has a full 3D
neighbourhood. `cube_interior_iff`: that first happens at `n = 3`. This selects the `3×3×3`
cube used for the confined carrier (`ConfinedCarrier`), the neutron's finite spectral channel
(`PMHadrons.NeutronPrediction`) and the nuclear packing and charge lattices
(`PMAtoms.NuclearPacking3D`, `PMAtoms.LatticeCharge3`). Moved from `PMHadrons` (Nov 2026).
-/

namespace PMAction.MinimalCube

/-- Vertices of the `n × n × n` cubic packing. -/
abbrev CubeVertex (n : Nat) := Fin n × Fin n × Fin n

/-! ## Which cube is physically valid?

A `2×2×2` cube is all boundary: no vertex has a full 3D neighbourhood.  A
volume-persistent cube needs at least one interior vertex.  That first happens at
`3×3×3`, whose centre is fully coordinated.  This is the persistence criterion
that selects the smallest valid lattice for the charge calculation.
-/

/-- A coordinate is on the boundary if it is `0` or `n−1`. -/
def coordBoundary (n : Nat) (i : Fin n) : Prop :=
  i.val = 0 ∨ i.val = n - 1

/-- A cube vertex is on the boundary if any coordinate is. -/
def cubeBoundary (n : Nat) (v : CubeVertex n) : Prop :=
  coordBoundary n v.1 ∨ coordBoundary n v.2.1 ∨ coordBoundary n v.2.2

/-- A cube vertex is interior if it is not on the boundary. -/
def cubeInterior (n : Nat) (v : CubeVertex n) : Prop :=
  ¬ cubeBoundary n v

/-- **The smallest volume-persistent cube is `3×3×3`.**  An interior vertex
exists exactly when `3 ≤ n`. -/
theorem cube_interior_iff (n : Nat) :
    (∃ v : CubeVertex n, cubeInterior n v) ↔ 3 ≤ n := by
  constructor
  · rintro ⟨v, hv⟩
    simp [cubeInterior, cubeBoundary, coordBoundary] at hv
    omega
  · intro hn
    refine ⟨(⟨1, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [cubeInterior, cubeBoundary, coordBoundary]
    omega

/-- The `2×2×2` cube has no interior vertex. -/
theorem cube_two_no_interior : ¬ (∃ v : CubeVertex 2, cubeInterior 2 v) := by
  intro h
  have := (cube_interior_iff 2).mp h
  omega

/-- The `3×3×3` cube has an interior vertex. -/
theorem cube_three_has_interior : ∃ v : CubeVertex 3, cubeInterior 3 v := by
  exact (cube_interior_iff 3).mpr (by norm_num)


/-- Computable boundary test for a coordinate. -/
def coordBoundaryB (n : Nat) (i : Fin n) : Bool :=
  i.val == 0 || i.val == n - 1

/-- Computable boundary test for a cube vertex. -/
def cubeBoundaryB (n : Nat) (v : CubeVertex n) : Bool :=
  coordBoundaryB n v.1 || coordBoundaryB n v.2.1 || coordBoundaryB n v.2.2

/-- Computable interior test for a cube vertex. -/
def cubeInteriorB (n : Nat) (v : CubeVertex n) : Bool :=
  !cubeBoundaryB n v

/-- Interior vertices of the `n×n×n` cube. -/
def interiorVertices (n : Nat) : Finset (CubeVertex n) :=
  (Finset.univ : Finset (CubeVertex n)).filter (fun v => cubeInteriorB n v = true)

/-- Boundary vertices of the `n×n×n` cube. -/
def boundaryVertices (n : Nat) : Finset (CubeVertex n) :=
  (Finset.univ : Finset (CubeVertex n)).filter (fun v => cubeBoundaryB n v = true)

theorem interiorVertices_three_card : (interiorVertices 3).card = 1 := by
  decide

theorem boundaryVertices_three_card : (boundaryVertices 3).card = 26 := by
  decide

theorem cubeVertices_three_card : (Finset.univ : Finset (CubeVertex 3)).card = 27 := by
  decide

end PMAction.MinimalCube
