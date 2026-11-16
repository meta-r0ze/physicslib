import PMAction.OtherWallStationary
import PMAction.NativeDetuning
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The other wall's flip as the library's lazy `β` event: the real root and its attempt probability

`OtherWallStationary.economy_selects`: Economy puts the other wall's flip on a root of
`δ³ = −κ_O0κ_O1κ_O2`. `NativeDetuning` identifies the on-site flip with the lazy native `β` event:
`δ = −gap(p)/2` with `p ∈ [0, 1/2)` its attempt probability, so `δ` is real and `≤ 0`.

* `real_root_unique`: two real cube roots of the same number are equal; the other two roots are
  `e^{±2πi/3}` times it, not real. With `κ_O0κ_O1κ_O2 = c > 0` the lazy event takes the real root
  `δ_c = −c^{1/3}` for every protocol (`lazy_root`).
* `attempt_probability`: the attempt probability `p = (1 − e^{−d})/2 ∈ (0, 1/2)` gives
  `−gap(p)/2 = −d`; with `d = c^{1/3}` it realizes `δ_c` (`attempt_realizes`).
* `offset_zero_mode`: the lazy event also leaves the wall-local offset `c' · 1` on the other wall
  (`NativeWallOffset`, `WallOffset`): light block `[[c', Mᴴ], [M, 0]]`. It still has a zero mode
  exactly when `M` is singular, now on the reference wall's side (`(0, y)` with `Mᴴ y = 0`), so the
  Economy selection is unchanged.

Open (PMAction REVIEW): the lazy reading changes the light mass law (`WallOffset`: masses near
`s²/c'` instead of the singular values `s`), and the EP readout so far uses singular values; which
reading the native event takes decides the mass law. With every protocol on the same real root,
up and down share the root (PMElementaryParticles OVERVIEW: `|V_us| ≈ 0.002` in that case for the bare
wire), so the flavour mixing must come from the readout, not from the roots.
-/

noncomputable section
namespace PMAction.OtherWallFlipEvent
open Matrix PMAction.RootTransferPhase

/-- **Real cube roots are unique.** -/
theorem real_root_unique (x y : ℝ) (h : x ^ 3 = y ^ 3) : x = y :=
  (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h

/-- **The lazy event takes the real root.** -/
theorem lazy_root (c x : ℝ) (hc : 0 < c) (hx : x ^ 3 = -c) : x = -c ^ ((1 : ℝ) / 3) := by
  apply real_root_unique
  rw [hx, neg_pow, ← Real.rpow_natCast (c ^ ((1 : ℝ) / 3)), ← Real.rpow_mul hc.le]
  norm_num

/-- The attempt probability that realizes a flip of size `d`. -/
def attempt (d : ℝ) : ℝ := (1 - Real.exp (-d)) / 2

theorem attempt_range {d : ℝ} (hd : 0 < d) : 0 < attempt d ∧ attempt d < 1 / 2 := by
  have h1 : Real.exp (-d) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h2 : 0 < Real.exp (-d) := Real.exp_pos _
  unfold attempt; constructor <;> linarith

theorem attempt_probability (d : ℝ) : -gap (attempt d) / 2 = -d := by
  unfold gap RootTransferPhase.residual attempt
  rw [show 1 - 2 * ((1 - Real.exp (-d)) / 2) = Real.exp (-d) by ring, Real.log_exp]
  ring

/-- The lazy event with this attempt probability realizes the resonant flip. -/
theorem attempt_realizes (c : ℝ) :
    -gap (attempt (c ^ ((1 : ℝ) / 3))) / 2 = -c ^ ((1 : ℝ) / 3) :=
  attempt_probability _

/-- **The wall-local offset keeps a zero mode exactly when `M` is singular**, on the reference
wall's side. -/
theorem offset_zero_mode (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) (y : Fin 3 → ℂ)
    (hy : Mᴴ *ᵥ y = 0) :
    fromBlocks (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) Mᴴ M 0 *ᵥ Sum.elim 0 y = 0 := by
  rw [fromBlocks_mulVec]
  simp [hy]

theorem offset_zero_mode_iff (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (∃ y : Fin 3 → ℂ, y ≠ 0 ∧ Mᴴ *ᵥ y = 0) ↔ M.det = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, det_conjTranspose, star_eq_zero]

end PMAction.OtherWallFlipEvent
