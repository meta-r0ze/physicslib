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
* `ledger_window`: the same measured window read as a band on `L₃` itself. Any `L₃` whose readout
  is within 3σ lies in `(11.66, 12.21)`.
* `candidates_in_window`: of the substrate counts that `PMConstants.ColourCount` lists, three sit
  in that band — `12` (the positive roots of D₄), `16η − 4` and the paper's
  `N_sys/(16η + 1/4)` — while `11` and `13` do not. The band has width about `0.55`, so the
  comparison cannot separate the three; the channel-count rule does.
* `ledger_in_window`: the derived ledger `12η` is in the band.
-/

namespace E8PConstants.StrongLedgerPulls

open PMConstants.Values

/-- Only the derived integer ledger lies within `3σ` of the measured coupling. -/
theorem integer_ledger_unique (L : ℕ) (hL : 0 < L) :
    |ledgerCoupling L - 0.1180| < 3 * 0.0009 ↔ L = 12 := by
  have h := alpha_footprint_bounds
  have hpos : (0 : ℝ) < PMConstants.Values.alpha * PMConstants.Values.footprint := by linarith [h.1]
  constructor
  · intro habs
    rcases lt_trichotomy L 12 with hl | hl | hl
    · exfalso
      have hL11 : (L : ℝ) ≤ 11 := by exact_mod_cast (by omega : L ≤ 11)
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hge : PMConstants.Values.alpha * PMConstants.Values.footprint / 11 ≤ ledgerCoupling L := by
        unfold ledgerCoupling
        exact div_le_div_of_nonneg_left hpos.le (by linarith) hL11
      have := (abs_lt.mp habs).2
      linarith [h.1]
    · exact hl
    · exfalso
      have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast (by omega : 13 ≤ L)
      have hle : ledgerCoupling L ≤ PMConstants.Values.alpha * PMConstants.Values.footprint / 13 := by
        unfold ledgerCoupling
        exact div_le_div_of_nonneg_left hpos.le (by norm_num) hL13
      have := (abs_lt.mp habs).1
      linarith [h.2]
  · rintro rfl
    have h12 := ledger_twelve
    rw [abs_lt]
    constructor <;> linarith [h12.1, h12.2]

/-- The measured window read as a band on the ledger. -/
theorem ledger_window {L : ℝ} (hL : 0 < L)
    (h : |PMConstants.Values.alpha * PMConstants.Values.footprint / L - 0.1180| < 3 * 0.0009) :
    11.66 < L ∧ L < 12.21 := by
  have hb := alpha_footprint_bounds
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · by_contra hc; push Not at hc
    have : PMConstants.Values.alpha * PMConstants.Values.footprint / 11.66 ≤
        PMConstants.Values.alpha * PMConstants.Values.footprint / L :=
      div_le_div_of_nonneg_left (by linarith [hb.1]) hL hc
    have h3 : (0.1207 : ℝ) < PMConstants.Values.alpha * PMConstants.Values.footprint / 11.66 := by
      rw [lt_div_iff₀ (by norm_num)]; linarith [hb.1]
    linarith
  · by_contra hc; push Not at hc
    have : PMConstants.Values.alpha * PMConstants.Values.footprint / L ≤
        PMConstants.Values.alpha * PMConstants.Values.footprint / 12.21 :=
      div_le_div_of_nonneg_left (by linarith [hb.1]) (by norm_num) hc
    have h3 : PMConstants.Values.alpha * PMConstants.Values.footprint / 12.21 < (0.1153 : ℝ) := by
      rw [div_lt_iff₀ (by norm_num)]; linarith [hb.2]
    linarith

/-- Three structurally different substrate counts sit in the band; `11` and `13` do not. -/
theorem candidates_in_window :
    (11.66 : ℝ) < 12 ∧ (11.66 : ℝ) < 16 * overhead - 4 ∧ 16 * overhead - 4 < 12.21 ∧
      (11.66 : ℝ) < strongWorkload ∧ strongWorkload < 12.21 ∧
      ¬ ((11.66 : ℝ) < 11) ∧ ¬ ((13 : ℝ) < 12.21) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [PMConstants.overhead, PMConstants.GaugeStiffness.strongWorkload,
      PMConstants.footprint]

/-- The derived ledger is in the band. -/
theorem ledger_in_window : (11.66 : ℝ) < colourLedger ∧ colourLedger < 12.21 := by
  rw [colour_ledger]; constructor <;> norm_num

end E8PConstants.StrongLedgerPulls
