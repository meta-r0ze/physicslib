import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# A certain transfer fixes a rate only with the event's duration

`NodeAmplitude` normalizes the vector-class carrier to admittance `K = 1`: an in-cycle event passes
with certainty. `CarrierFlip` puts a carrier of hop amplitude `t` (a Hamiltonian rate) in the
chirality-flip slot as `−r t/2`. These are different quantities: admittance is a transmission
probability per event (`PMConstants.HandoffAdmittance`), `t` is a rate.

Under an update `e^{−iτH}` (the open PMAction item "Update as `e^{−iHt}` on wall modes"), a coupling
`t` between two states acting for a time `τ` transfers with probability `sin²(tτ)`
(`exp(−iτ t σ) = cos(tτ) − i sin(tτ) σ`).

* `certain_iff`: the transfer is certain exactly when `cos(tτ) = 0`.
* `certain_min`: then `tτ ≥ π/2` (for `tτ > 0`): a certain event of duration `τ` has rate at least
  `π/(2τ)`.
* `flip_lower`: so the carrier's flip is at least `r π/(4τ)`.

**Consequence for the wire (PMAction REVIEW, event-clock item).** The light-mode reduction and a heavy
state that persists on its walls need the vector flip small against the crossing, `K_f ≪ |y| = 1`.
With a certain vector event this needs `τ ≫ π/4` in hop-time units: one carrier event lasts many
hop times. With the update's tick `τ₀` small (the split update needs it, `GlobalTickInterval`), a
carrier event spans many ticks. The library fixes neither the tick nor an event's duration in hop
units ("Physical refinement/clock … remain open", OVERVIEW). So `t_v` is open, and the statement to
derive is the duration of one carrier event.

Falsification: a derivation that a carrier event completes within one hop time (`τ ≲ 1`) gives
`K_f ≳ 1`, which breaks the reduction and the heavy state's persistence on its walls
(`ChiralLightBand`'s premise that light states lie far below the wall gap). The weak refresh, which
acts every tick, is a sign exchange of carrier labels, not a carrier hop, so it does not fix `τ`.
-/

namespace PMAction.CertainTransferRate

/-- **A two-state transfer `sin²(tτ)` is certain exactly when `cos(tτ) = 0`.** -/
theorem certain_iff (θ : ℝ) : Real.sin θ ^ 2 = 1 ↔ Real.cos θ = 0 := by
  have h := Real.sin_sq_add_cos_sq θ
  constructor
  · intro hs
    have : Real.cos θ ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro hc
    rw [hc] at h
    linarith

/-- **The least positive phase of a certain transfer is `π/2`.** -/
theorem certain_min (θ : ℝ) (hθ : 0 < θ) (hc : Real.cos θ = 0) : Real.pi / 2 ≤ θ := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc
  have hp := Real.pi_pos
  have hk0 : (0 : ℤ) ≤ k := by
    by_contra hneg
    have h1 : k ≤ -1 := by omega
    have h2 : (k : ℝ) ≤ -1 := by exact_mod_cast h1
    have h3 : ((2 : ℝ) * k + 1) * Real.pi < 0 := mul_neg_of_neg_of_pos (by linarith) hp
    rw [hk] at hθ
    linarith
  have h4 : (0 : ℝ) ≤ k := by exact_mod_cast hk0
  have h5 : 0 ≤ (k : ℝ) * Real.pi := mul_nonneg h4 hp.le
  rw [hk]
  linarith

/-- **The flip of a certain carrier event of duration `τ` is at least `r π/(4τ)`.** -/
theorem flip_lower (r t τ : ℝ) (hr : 0 ≤ r) (hτ : 0 < τ) (hθ : 0 < t * τ)
    (hc : Real.cos (t * τ) = 0) : r * Real.pi / (4 * τ) ≤ r * t / 2 := by
  have h := certain_min (t * τ) hθ hc
  have ht : Real.pi / (2 * τ) ≤ t := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have : r * (Real.pi / (2 * τ)) ≤ r * t := mul_le_mul_of_nonneg_left ht hr
  calc r * Real.pi / (4 * τ) = r * (Real.pi / (2 * τ)) / 2 := by field_simp; ring
    _ ≤ r * t / 2 := by linarith

end PMAction.CertainTransferRate
