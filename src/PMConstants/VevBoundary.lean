import PMConstants.VevImpedance
import PMConstants.VevCorrections
import PMSubstrate.CapacityBarbier

/-! Boundary admittance from closure channels and the length of a constant-width envelope. -/

noncomputable section
namespace PMConstants.VevBoundary
open PMConstants.VevCorrections PMSubstrate.E8Values

/-- A constant-width envelope of width `w` has boundary length `π w` (Barbier). -/
theorem barbier_boundary (w : ℝ) : ∫ _ in (0)..(2 * Real.pi), w / 2 = Real.pi * w :=
  PMSubstrate.Capacity.barbier (fun _ => w / 2) continuous_const w (fun _ => by ring)

/-- `n` closure channels in parallel, each of impedance `πw` (the boundary of a width-`w`
envelope). -/
def parallelClosures (n w : ℝ) : ℝ := n / (Real.pi * w)

/-- The same channels in series. -/
def seriesClosures (n w : ℝ) : ℝ := 1 / (n * (Real.pi * w))

theorem boundary_is_parallel_closures :
    VevImpedance.boundary = parallelClosures (chi : ℝ) (D : ℝ) := by
  unfold VevImpedance.boundary parallelClosures; ring

end PMConstants.VevBoundary
