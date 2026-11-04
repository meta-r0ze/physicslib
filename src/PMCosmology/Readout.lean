import PMCosmology.Background
import PMAction.Continuity

/-!
# The scale-factor readout, and the matter equation of state

B1/B2 of the review ask where the scale factor `a` and the density come from.
This module makes the readout explicit as a *coarse-grained comoving cell*: a cell
of physical volume `V = a³` carrying a conserved charge `N`. The scale factor is
by definition the cube root of the cell volume (`a_cube : a³ = V`), and the density
is `N/V`, which is exactly PM-2's `Continuity.homogeneousDensity N a`.

Reusing PM-2 (`PMAction.Continuity`), the density then obeys the matter continuity
law and has `w = 0` — so the equation of state follows from the conservation of
`N` plus the volume readout, not from a separate assumption.

Still inputs: the *value* of `V` (the expansion history) and that the conserved
charge is a number (not yet an energy with its own per-particle scaling). The
readout does not derive the expansion; it fixes what `a` means.
-/

noncomputable section
namespace PMCosmology.Readout

/-- A coarse-grained homogeneous cell: physical volume `V = a³`, carrying a
conserved charge `N`. -/
structure HomogeneousReadout where
  N : ℝ
  V : ℝ
  a : ℝ
  a_pos : 0 < a
  a_cube : a ^ 3 = V
  N_pos : 0 < N

namespace HomogeneousReadout
variable (H : HomogeneousReadout)

/-- Charge density of the cell. -/
def density : ℝ := H.N / H.V

/-- It is the PM-2 conserved-charge density `N/a³`. -/
theorem density_eq : H.density = PMAction.Continuity.homogeneousDensity H.N H.a := by
  unfold density PMAction.Continuity.homogeneousDensity
  rw [← H.a_cube]

theorem density_pos : 0 < H.density := by
  unfold density
  exact div_pos H.N_pos (by rw [← H.a_cube]; exact pow_pos H.a_pos 3)

/-- **Matter continuity** for the readout, from PM-2 conservation. -/
theorem continuity :
    H.a * deriv (PMAction.Continuity.homogeneousDensity H.N) H.a
      + 3 * PMAction.Continuity.homogeneousDensity H.N H.a = 0 :=
  PMAction.Continuity.matter_continuity H.N H.a (ne_of_gt H.a_pos)

/-- **Matter equation of state** `w = 0`, from conservation plus the volume readout. -/
theorem w_matter :
    -1 - H.a * deriv (PMAction.Continuity.homogeneousDensity H.N) H.a
        / (3 * PMAction.Continuity.homogeneousDensity H.N H.a) = 0 :=
  PMAction.Continuity.matter_w H.N H.a (ne_of_gt H.N_pos) (ne_of_gt H.a_pos)

end HomogeneousReadout

end PMCosmology.Readout
