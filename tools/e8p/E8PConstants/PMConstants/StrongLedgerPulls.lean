import PMConstants.Values

/-!
# Strong-ledger measured comparison (moved from the PMConstants leaf)

The colour ledger is derived from the channel count: colour links maintain the payload of the
channels they act on and exactly `12` of the sixteen channels carry colour, so `L₃ = 12η`
(`PMConstants.ColourChannels.coloured_channels`, `colour_ledger`). The integer readout and its
separation stay in `PMConstants.StrongLedgerTest`; the comparison with the measured coupling is
here.

* `integer_ledger_unique`: among positive integers, `L₃ = 12` is the only one whose readout lies
  within three standard deviations of `α_s(M_Z) = 0.1180 ± 0.0009` (PDG 2024). Every `L₃ ≤ 11`
  gives more than `0.1279`; every `L₃ ≥ 13` gives less than `0.1083`. Integers in this range are
  about 8% apart, so landing within 3σ of one is a falsifiability check, not evidence.
-/

namespace E8PConstants.StrongLedgerPulls

open PMConstants.Values

/-- Only the derived integer ledger lies within `3σ` of the measured coupling. -/
theorem integer_ledger_unique (L : ℕ) (hL : 0 < L) :
    |ledgerCoupling L - 0.1180| < 3 * 0.0009 ↔ L = 12 := by
  have h := alpha_footprint_bounds
  have hpos : (0 : ℝ) < PMConstants.Values.α * PMConstants.Values.footprint := by linarith [h.1]
  constructor
  · intro habs
    rcases lt_trichotomy L 12 with hl | hl | hl
    · exfalso
      have hL11 : (L : ℝ) ≤ 11 := by exact_mod_cast (by omega : L ≤ 11)
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hge : PMConstants.Values.α * PMConstants.Values.footprint / 11 ≤ ledgerCoupling L := by
        unfold ledgerCoupling
        exact div_le_div_of_nonneg_left hpos.le (by linarith) hL11
      have := (abs_lt.mp habs).2
      linarith [h.1]
    · exact hl
    · exfalso
      have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast (by omega : 13 ≤ L)
      have hle : ledgerCoupling L ≤ PMConstants.Values.α * PMConstants.Values.footprint / 13 := by
        unfold ledgerCoupling
        exact div_le_div_of_nonneg_left hpos.le (by norm_num) hL13
      have := (abs_lt.mp habs).1
      linarith [h.2]
  · rintro rfl
    have h12 := ledger_twelve
    rw [abs_lt]
    constructor <;> linarith [h12.1, h12.2]

end E8PConstants.StrongLedgerPulls
