import Mathlib.Tactic

/-!
# The lazy `β` event leaves an energy offset on its wall

`NativeDetuning.generator_split`: the lazy-transfer generator of a wall's `β` event is
`(gap/2) · 1 − (gap/2) · β`. With no event on the reference's wall (`p_R = 0`) and one on the other
wall (`p_O > 0`), the identity part is not a global offset: it is `c · P_O` with `c = gap(p_O)/2 = |δ_O|`,
an energy on the other wall only. `NativeWallOffset` proves that this term is a global scalar
only at zero coefficient, and that it commutes with the coupled Hamiltonian only at zero coefficient
or zero crossing. Removing it through a time-dependent wall frame also transforms the crossing.
The following mass readings have different event premises.

1. **Lazy event (the library's `RootTransferPhase` reading).** The other wall's light mode sits at
   energy `c = |δ_O|`. The light block becomes `[[c, Mᴴ], [M, 0]]`; for a singular value `s` of `M`
   its eigenvalues solve `λ² − c λ − s² = 0` (`offset_char`), the larger root is `≥ c` and the
   smaller has `|λ₋| ≤ s²/c` (`seesaw_bound`). Since `s ≈ |d| |δ_O|` with `|d| ≪ 1`, the left-handed
   light masses are `≈ s²/|δ_O|`: the squares of the wire's singular values over `|δ_O|`.
2. **Coherent rotation (traceless generator `θ β`).** No offset; the masses are the singular values
   `s` (the reading used so far, `ReferenceWallMass`, `WireMass`).

Checked numerically on the full two-wall Hamiltonian: with the offset the six light energies split
into three near `c` and three far below the `c = 0` values. So the reading changes every mass ratio
(squared), while `U` (the eigenvectors of `M Mᴴ`, `ReferenceWallRotation`) is the same in both.
Which reading is native decides the mass formula; the library's current identification of `δ` with
a lazy event (`NativeDetuning`) picks reading 1.
-/

namespace PMAction.WallOffset

/-- **The offset light block's eigenvalue equation**: `det [[c − λ, s], [s, −λ]] = λ² − cλ − s²`. -/
theorem offset_char (c s l : ℝ) : (c - l) * (-l) - s * s = l ^ 2 - c * l - s ^ 2 := by ring

/-- **Seesaw bound**: if `λ₊ ≥ c > 0` and `λ₊ λ₋ = −s²`, then `|λ₋| ≤ s²/c`. -/
theorem seesaw_bound (c s lp lm : ℝ) (hc : 0 < c) (hp : c ≤ lp) (hprod : lp * lm = -s ^ 2) :
    |lm| ≤ s ^ 2 / c := by
  have hlp : 0 < lp := lt_of_lt_of_le hc hp
  have hlm : lm = -s ^ 2 / lp := by field_simp; linarith
  rw [hlm, abs_div, abs_neg, abs_of_nonneg (sq_nonneg s), abs_of_pos hlp]
  exact div_le_div_of_nonneg_left (sq_nonneg s) hc hp

end PMAction.WallOffset
