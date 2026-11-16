import PMAction.WireMass
import PMAction.ReferenceDetuning
import PMAction.PersistenceSelection
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

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

**Selection by Economy** (`economy_selects`, `selected_flip`). Paper I's survival law makes the most
persistent option the cheapest (`PersistenceSelection`), and the cheapest configurations are the
stationary ones, as for the reference background (`PersistentBackground`). Taking the other wall's
flip together with a light state as the option, and any price that is nonnegative and zero exactly on
stationary states (`energyPrice`, the state's squared energy, is one), the most persistent options are
exactly the stationary light states, and their flip is a root of `δ³ = −κ_O0κ_O1κ_O2` (a root exists,
`root_exists`). With `κ_O = (K, k, k)`, `|δ_O| = (K k²)^{1/3}`. PMElementaryParticles finds every
charged protocol's light-ratio fit within a few percent of the real root
(`tools/protocol_readout_scan.py`); the light masses are then corrections to an exactly massless wire
mode. Inputs: the flip is free to take the value persistence selects (it is part of the option), and
`κ_O` is fixed. As the lazy `β` event it is the real root (`OtherWallFlipEvent`).
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

/-! ## Economy selects the resonance

`PersistenceSelection.most_persistent_iff_cheapest`: under Paper I's survival law the most persistent
option is the cheapest. `NativeReferenceBackground.minimum_iff_fixed` / `PersistentBackground`: the
cheapest configurations are exactly the stationary ones (zero excess price). Apply the same to the
other wall's light states: a trial state `v` at flip `δ` pays a price `p δ v ≥ 0` that is zero exactly
when the state is stationary under the light block (`M v = 0`); the flip is part of the option. -/

/-- A resonant flip exists: `−κ_O0κ_O1κ_O2` has a cube root in `ℂ`. -/
theorem root_exists (κO : Fin 3 → ℂ) : ∃ δ : ℂ, δ ^ 3 = -(κO 0 * κO 1 * κO 2) :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

/-- **Economy selects a stationary light state, hence the resonant flip.** Among all pairs (flip,
nonzero light state) with a price that is nonnegative and zero exactly on stationary states, the most
persistent pairs are exactly those with `M v = 0`; their flip solves `δ³ = −κ_O0κ_O1κ_O2`. -/
theorem economy_selects (κR κO : Fin 3 → ℂ) (hR : ∀ i, κR i ≠ 0)
    (p : ℂ → (Fin 3 → ℂ) → ℝ) (hp0 : ∀ δ v, 0 ≤ p δ v)
    (hpz : ∀ δ v, p δ v = 0 ↔ mass δ κR κO *ᵥ v = 0) (β : ℝ) (hβ : 0 < β)
    (δ : ℂ) (v : Fin 3 → ℂ) :
    (∀ (δ' : ℂ) (v' : Fin 3 → ℂ), v' ≠ 0 →
        Real.exp (-β * p δ' v') ≤ Real.exp (-β * p δ v)) ↔
      mass δ κR κO *ᵥ v = 0 := by
  have hanti := PMAction.PersistenceSelection.survival_strictAnti β hβ
  constructor
  · intro h
    obtain ⟨δc, hc⟩ := root_exists κO
    obtain ⟨w, hw, hMw⟩ := (massless_iff δc κR κO hR).mpr hc
    have hle : p δ v ≤ p δc w := hanti.le_iff_ge.mp (h δc w hw)
    have hz : p δc w = 0 := (hpz δc w).mpr hMw
    exact (hpz δ v).mp (le_antisymm (hz ▸ hle) (hp0 δ v))
  · intro hM δ' v' _
    apply hanti.antitone
    rw [(hpz δ v).mpr hM]
    exact hp0 δ' v'

/-- The selected flip is resonant. -/
theorem selected_flip (κR κO : Fin 3 → ℂ) (hR : ∀ i, κR i ≠ 0) (δ : ℂ) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) (hM : mass δ κR κO *ᵥ v = 0) : δ ^ 3 = -(κO 0 * κO 1 * κO 2) :=
  (massless_iff δ κR κO hR).mp ⟨v, hv, hM⟩

/-- A price with the required properties: the squared norm of the light block's action on the state
(the state's energy squared, to light-band order). -/
def energyPrice (κR κO : Fin 3 → ℂ) (δ : ℂ) (v : Fin 3 → ℂ) : ℝ :=
  ∑ i, Complex.normSq ((mass δ κR κO *ᵥ v) i)

theorem energyPrice_nonneg (κR κO : Fin 3 → ℂ) (δ : ℂ) (v : Fin 3 → ℂ) :
    0 ≤ energyPrice κR κO δ v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem energyPrice_zero_iff (κR κO : Fin 3 → ℂ) (δ : ℂ) (v : Fin 3 → ℂ) :
    energyPrice κR κO δ v = 0 ↔ mass δ κR κO *ᵥ v = 0 := by
  unfold energyPrice
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)]
  constructor
  · intro h; funext i; exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h _ _; rw [h]; simp

end PMAction.OtherWallStationary
