import PMAction.CertainTransferRate

/-!
# A rate from an admittance needs the event's duration

`ReferenceNode` eliminates the reference node and fixes the restoring crossing relative to the
in-cycle one, `k/K = α/2`, where `NodeAmplitude` normalizes the in-cycle carrier to admittance
`K = 1`. So that value is pinned against an **admittance**: a transfer probability per event.
The wire of `WireResonanceSpectrum` needs the reference row `(1, k, k)` in **rates**: Hamiltonian
coefficients. `CertainTransferRate` shows these are different quantities, and supplies the bridge:
a supplied transfer probability fixes the principal pulse area `θ = arcsin √w`
(`principal_transfer_area`), and a rate is an area divided by a duration.

* `area`, `area_one`: the principal area of a transfer probability; a certain transfer has area
  `π/2`, which is `CertainTransferRate.certain_min`'s least phase.
* `rate_ratio`: for two insertions of areas `w₂`, `w₁` and durations `τ₂`, `τ₁`, the rate ratio is
  `(area w₂ / area w₁) · (τ₁ / τ₂)`. The durations do not cancel in general.
* `rate_ratio_common_duration`: they cancel when the two insertions last the same time, leaving
  the area ratio alone. `CertainTransferRate.common_tick_rate_ratio` is the same cancellation
  stated on ticks.
* `restoringRate`: the common-duration reading of an admittance `w` against the certain in-cycle
  crossing, `(2/π) arcsin √w`.
* `lt_arcsin`, `arcsin_lt`: two-sided enclosure of the area, used for numbers downstream.

So the wire's `k` is `restoringRate (α/2)` only if the restoring insertion and the certain
crossing last the same time. Otherwise `k = restoringRate (α/2) · (τ_certain / τ_restoring)`, and
the duration ratio is exactly the open quantity of `CertainTransferRate`: the duration of one
carrier event. Reading `k = α/2` directly is neither — it uses a probability where a rate belongs.
-/

noncomputable section
namespace PMAction.CarrierRateFromAdmittance

/-- The principal pulse area that realizes a transfer probability. -/
def area (w : ℝ) : ℝ := Real.arcsin (Real.sqrt w)

/-- **A certain transfer has area `π/2`.** -/
theorem area_one : area 1 = Real.pi / 2 := by
  rw [area, Real.sqrt_one, Real.arcsin_one]

/-- The area is what a supplied transfer probability fixes. -/
theorem area_of_transfer {θ w : ℝ} (hθ : 0 ≤ θ) (hprincipal : θ ≤ Real.pi / 2)
    (hw : Real.sin θ ^ 2 = w) : θ = area w :=
  CertainTransferRate.principal_transfer_area hθ hprincipal hw

/-- A rate is a pulse area over a duration. -/
def rate (w τ : ℝ) : ℝ := area w / τ

/-- **The rate ratio of two insertions carries their duration ratio.** -/
theorem rate_ratio (w₁ w₂ τ₁ τ₂ : ℝ) (hτ₁ : τ₁ ≠ 0) (hτ₂ : τ₂ ≠ 0) (h₁ : area w₁ ≠ 0) :
    rate w₂ τ₂ / rate w₁ τ₁ = area w₂ / area w₁ * (τ₁ / τ₂) := by
  unfold rate
  field_simp
  ring

/-- **A common duration cancels, leaving the area ratio.** -/
theorem rate_ratio_common_duration (w₁ w₂ τ : ℝ) (hτ : τ ≠ 0) (h₁ : area w₁ ≠ 0) :
    rate w₂ τ / rate w₁ τ = area w₂ / area w₁ := by
  rw [rate_ratio w₁ w₂ τ τ hτ hτ h₁, div_self hτ, mul_one]

/-- The common-duration rate of an admittance against the certain in-cycle crossing. -/
def restoringRate (w : ℝ) : ℝ := area w / (Real.pi / 2)

theorem restoringRate_eq (w : ℝ) :
    restoringRate w = 2 / Real.pi * Real.arcsin (Real.sqrt w) := by
  rw [restoringRate, area, div_div_eq_mul_div, eq_div_iff Real.pi_ne_zero]
  field_simp

/-- **The certain crossing is the unit of that reading.** -/
theorem restoringRate_one : restoringRate 1 = 1 := by
  rw [restoringRate, area_one, div_self (by positivity)]

/-! ## Enclosing the area -/

/-- **The area exceeds the amplitude.** -/
theorem lt_arcsin {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : y < Real.arcsin y := by
  have hpos : 0 < Real.arcsin y := Real.arcsin_pos.mpr hy
  have h := Real.sin_lt hpos
  rwa [Real.sin_arcsin (by linarith) hy1] at h

/-- **A cubic upper bound for the area.** -/
theorem arcsin_lt {y b : ℝ} (hy : -1 ≤ y) (hb : 0 < b) (hb2 : b ≤ Real.pi / 2)
    (h : y < b - b ^ 3 / 6) : Real.arcsin y < b := by
  have hs : b - b ^ 3 / 6 < Real.sin b := Real.sin_gt_sub_cube hb
  have hlt : y < Real.sin b := h.trans hs
  calc Real.arcsin y < Real.arcsin (Real.sin b) :=
        Real.arcsin_lt_arcsin hy hlt (Real.sin_le_one b)
    _ = b := Real.arcsin_sin (by linarith [Real.pi_pos]) hb2

end PMAction.CarrierRateFromAdmittance
