import PMAction.WireMass
import PMAction.ReferenceDetuning

/-!
# The other wall's flip: a stationary light state on each wall

`ReferenceDetuning`: the reference persists as a stationary zero mode of the same update the
flavour fermions see, so the reference wall has no on-site flip (`δ_R = 0`); with both walls
undetuned on a single label the mass ordering reverses (`UndetunedWall`), so `δ_O ≠ 0` and no single
label of the other wall is stationary. With the three labels coupled by the wire
(`WireMass.mass δ κ_R κ_O = diag κ_R · (δ + cyc κ_O)`) the other wall can still carry a stationary
light state, a superposition over labels.

* `det_factor`: `det M = κ_R0κ_R1κ_R2 (δ − δ_c)(δ² + δδ_c + δ_c²)` when `δ_c³ = −κ_O0κ_O1κ_O2`.
* `massless_iff`: with nonzero `κ_R`, the wire has a massless mode exactly when
  `δ³ = −κ_O0κ_O1κ_O2` (the real root `δ_c = −(κ_O0κ_O1κ_O2)^{1/3}` and its rotations by `e^{±2πi/3}`).
* `null_vector`: then `v = (1, −κ_O0/δ, κ_O0κ_O1/δ²)` is annihilated by `M`: every label is
  occupied (`null_all_labels`), so the stationary state is not a single-label state.
* `light_zero_mode`: `(v, 0)` is a zero mode of the light block `[[0, Mᴴ], [M, 0]]` (other wall
  first): a stationary state on the other wall.
* `flip_nonzero`: with a nonzero cycle product, `δ = 0` is not a root.

**Selection (premise).** If each wall carries a stationary light state, as the reference wall does,
the other wall's flip is a root of `δ³ = −κ_O0κ_O1κ_O2`: with `κ_O = (K, k, k)`,
`|δ_O| = (K k²)^{1/3}`. This replaces the free `δ_O` per protocol. PMElementaryParticles tests it: the
light-ratio fits of all three charged protocols sit within a few percent of this root
(`tools/protocol_readout_scan.py`). The light masses are then corrections to an exactly massless
wire mode. Not derived here: the microscopic event that realizes the flip.
-/

noncomputable section
namespace PMAction.OtherWallStationary
open Matrix PMAction.WireMass PMAction.ReferenceWallRotation

theorem det_factor (δ δc : ℂ) (κR κO : Fin 3 → ℂ) (hc : δc ^ 3 = -(κO 0 * κO 1 * κO 2)) :
    (mass δ κR κO).det = κR 0 * κR 1 * κR 2 * ((δ - δc) * (δ ^ 2 + δ * δc + δc ^ 2)) := by
  rw [det_mass]
  have : κO 0 * κO 1 * κO 2 = -δc ^ 3 := by rw [hc]; ring
  rw [this]; ring

theorem massless_iff (δ : ℂ) (κR κO : Fin 3 → ℂ) (hR : ∀ i, κR i ≠ 0) :
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧ mass δ κR κO *ᵥ v = 0) ↔ δ ^ 3 = -(κO 0 * κO 1 * κO 2) := by
  rw [Matrix.exists_mulVec_eq_zero_iff, det_mass]
  have h : κR 0 * κR 1 * κR 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hR 0) (hR 1)) (hR 2)
  rw [mul_eq_zero, or_iff_right h, add_eq_zero_iff_eq_neg]

theorem flip_nonzero (κO : Fin 3 → ℂ) (hO : κO 0 * κO 1 * κO 2 ≠ 0) (δ : ℂ)
    (hδ : δ ^ 3 = -(κO 0 * κO 1 * κO 2)) : δ ≠ 0 := by
  rintro rfl
  apply hO
  have : (0 : ℂ) = -(κO 0 * κO 1 * κO 2) := by simpa using hδ
  linear_combination this

/-- The other wall's stationary light state. -/
def nullVec (δ : ℂ) (κO : Fin 3 → ℂ) : Fin 3 → ℂ := ![1, -κO 0 / δ, κO 0 * κO 1 / δ ^ 2]

theorem null_vector (δ : ℂ) (κR κO : Fin 3 → ℂ) (hδ0 : δ ≠ 0)
    (hδ : δ ^ 3 = -(κO 0 * κO 1 * κO 2)) : mass δ κR κO *ᵥ nullVec δ κO = 0 := by
  have hX : PMAction.ReferenceWallRotation.X δ (shift κO) *ᵥ nullVec δ κO = 0 := by
    ext i; fin_cases i <;>
      simp [PMAction.ReferenceWallRotation.X, shift, PMAction.CyclicSeesaw.cyc, nullVec, mulVec, dotProduct, Fin.sum_univ_three]
    · field_simp; linear_combination hδ
    · field_simp; ring
    · field_simp; ring
  rw [mass, ← mulVec_mulVec, hX, mulVec_zero]

theorem null_all_labels (δ : ℂ) (κO : Fin 3 → ℂ) (hδ0 : δ ≠ 0) (h0 : κO 0 ≠ 0) (h1 : κO 1 ≠ 0) :
    ∀ i, nullVec δ κO i ≠ 0 := by
  intro i; fin_cases i <;> simp [nullVec, hδ0, h0, h1]

/-- The light block, other wall first. -/
def lightBlock (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ :=
  fromBlocks 0 Mᴴ M 0

theorem light_zero_mode (δ : ℂ) (κR κO : Fin 3 → ℂ) (hδ0 : δ ≠ 0)
    (hδ : δ ^ 3 = -(κO 0 * κO 1 * κO 2)) :
    lightBlock (mass δ κR κO) *ᵥ Sum.elim (nullVec δ κO) 0 = 0 := by
  rw [lightBlock, fromBlocks_mulVec]
  simp [null_vector δ κR κO hδ0 hδ]

end PMAction.OtherWallStationary
