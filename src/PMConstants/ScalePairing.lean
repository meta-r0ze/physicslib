import PMConstants.ReadoutScales

/-!
# Which electric coupling the colour formula pairs with `α_s(M_Z)`

The colour formula is `α_s = α · N_sys / (12η)`. If both couplings were read at the same scale `M_Z`,
the electric one would be `α(M_Z)`, with `1/α(M_Z)` in `(127.94, 127.96)`.

* `same_scale_excluded`: then `α_s > 0.1263`, more than `9σ` above `0.1180 ± 0.0009`.
* `ColourReference.strong_from_payload`: with `α(0)` the formula gives `0.11799 < α_s < 0.11800`.

So the formula is a relation between each coupling at its own matching point: `α` where the
electric readout is maintained (zero momentum, `Q` unbroken) and `α_s` at the `Z`. The ledgers are
scale-free counts per phase, and this pairing is what the data keep. Why the ledger ratio relates
the two matching-point values, rather than same-scale values, is not derived here.
-/

noncomputable section
namespace PMConstants.ScalePairing
open PMConstants

theorem same_scale_excluded {aZ : ℝ} (h : 1 / 127.96 < aZ ∧ aZ < 1 / 127.94) :
    0.1263 < aZ * footprint / ColourChannels.colourLedger ∧
      9 < (aZ * footprint / ColourChannels.colourLedger - 0.1180) / 0.0009 := by
  have hf : footprint / ColourChannels.colourLedger = 8295 / 43 / (12 * (171 / 172)) := by
    norm_num [footprint, ColourChannels.colourLedger, overhead]
  have e : aZ * footprint / ColourChannels.colourLedger = aZ * (8295 / 43 / (12 * (171 / 172))) := by
    rw [mul_div_assoc, hf]
  rw [e]
  constructor
  · nlinarith [h.1]
  · rw [lt_div_iff₀ (by norm_num)]; nlinarith [h.1]

end PMConstants.ScalePairing
