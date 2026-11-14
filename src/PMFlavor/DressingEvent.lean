import PMConstants.VevEvent
import PMFlavor.DressingChannels

/-!
# The dressing loss is an event, so the time axis carries none of it: `1/516`

`DressingChannels` reduced the dressing divisor to one question: does the time axis's share of the
reference deficit `1 − η = 1/172` leave the CKM block (`1/516` per row) or stay with the reference
(`1/688`)? The VEV faced the same question for its noise divisor (`3` versus `4`), and
`PMConstants.VevEvent` settled it from the event principle (`DepthEvents.no_event_no_advance`):
along the time axis the comparison of the maintained reference with its transport is the
maintenance update itself, exact repair returns the reference, and that comparison never fires
(`VevEvent.time_never_fires`).

The dressing is a transfer: probability leaves the three-generation block into the outlet channels
(`CKMDressing.dilation_needs_three`, `DressingChannels.dilation_three`), so it is registered, an
event. The same principle applies.

* `event_law_spatial`: whatever the prior law `π` over the four axes, the law of the axis given that
  a loss event occurred, `πᵢfᵢ/Σπⱼfⱼ` with event rate `f₀ = 0` on the time axis, has no weight on
  time (as in `VevEvent.conditioned_on_event`); with the three spatial axes equivalent, each
  carries exactly `1/3`.
* `deficit_per_channel`: so each spatial outlet carries `(1 − η)/3 = 1/516` of the deficit, and in
  the minimal dilation (row `i` into channel `i`) each CKM row loses `1/516`.
* `per_direction_needs_time`: the per-direction share `(1 − η)/4 = 1/688` is the uniform four-axis
  law, which needs weight `1/4` on the time axis, i.e. the time comparison firing.

Premise: the dressing loss is registered (an event), as the VEV readout is. Data: the first-row sum
`1 − 1/516 = 0.99806` lies `0.5σ` from `0.9984 ± 0.0007` (`CabibboDressing.direction_shares_fit`).
The library's value `q² = 687/688` (`CKMDressing.q2`, `Mixing.dressing`, `Values`) is the
four-axis share; under this derivation it becomes `515/516`.
-/

namespace PMFlavor.DressingEvent

theorem event_law_spatial (π f : Fin 4 → ℝ) (hf0 : f 0 = 0) (hZ : 0 < ∑ j, π j * f j)
    (h12 : π 1 * f 1 = π 2 * f 2) (h13 : π 1 * f 1 = π 3 * f 3) :
    π 0 * f 0 / (∑ j, π j * f j) = 0 ∧ π 1 * f 1 / (∑ j, π j * f j) = 1 / 3 ∧
      π 2 * f 2 / (∑ j, π j * f j) = 1 / 3 ∧ π 3 * f 3 / (∑ j, π j * f j) = 1 / 3 := by
  have hs : ∑ j, π j * f j = 3 * (π 1 * f 1) := by
    simp only [Fin.sum_univ_four, hf0, mul_zero, zero_add]
    linarith
  have hp : 0 < π 1 * f 1 := by linarith
  rw [hs]
  refine ⟨by simp [hf0], ?_, ?_, ?_⟩
  · field_simp; exact div_self hp.ne'
  · rw [← h12]; field_simp; exact div_self hp.ne'
  · rw [← h13]; field_simp; exact div_self hp.ne'

theorem deficit_per_channel : (1 / 172 : ℝ) * (1 / 3) = 1 / 516 := by norm_num

theorem per_direction_needs_time (q : Fin 4 → ℝ) (h : ∀ i, q i = 1 / 4) : q 0 ≠ 0 := by
  rw [h]; norm_num

end PMFlavor.DressingEvent
