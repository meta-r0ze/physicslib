import PMConstants.ColourCount

/-!
# Colour refreshes the coloured channels: `L₃ = 12η`

Paper III's footprint per phase is `N_sys = 172 + 16η + 5`: clock row `43`, three spatial rows
`129`, payload `16η` (sixteen channels, each carrying `η` because one of the `172` slots is the
reference), and wires `σ = 5`. The electroweak readouts take `e` from the whole footprint and
SU(2) from the clock row. This module asks what colour links act on.

* `coloured_channels`: of the sixteen channels of a generation (multiplicities `6, 3, 3, 2, 1, 1`
  for `Q, u, d, L, e, ν`), exactly `12` carry colour and `4` do not.
* Rule (colour ledger). Colour links maintain the payload of the channels they act on, so the
  colour workload is that payload: `L₃ = 12η = 513/43` (`colour_ledger`). Using the bare count `12`
  would drop the reference overhead that the same footprint charges to every payload channel.
* `strong_from_channels`: `0.11799 < α N_sys/(12η) < 0.11800`, inside the window of
  `ColourCount.ledger_window` and within `0.01σ` of `0.1180 ± 0.0009`. The data window has width
  about `0.55` in `L₃`, so this agreement alone is not evidence; the rule is.
* `close_to_paper`: the paper's `(16η + 1/4)α` differs from the ledger value by less than
  `0.0001`, so the ledger form replaces it without moving the comparison.
* `weak_not_per_channel`: the same per-channel rule for SU(2) (eight left-handed channels, `8η`)
  would give a mixing below `0.042`. SU(2)'s ledger is the clock row, not its channels.

So the two non-abelian sectors refresh different resources: SU(2) the clock (the chiral sector
carries the arrow of time), SU(3) the coloured payload (vector-like, independent of time
orientation). Deriving that assignment from the update is the remaining premise; with it, the
weak premise `W = Δ` of `GaugeStiffness` and the colour ledger are one statement.
-/

noncomputable section
namespace PMConstants.ColourChannels
open PMConstants CertifiedConstants StrongLedgerTest

/-- Channel multiplicities per generation: `Q, u, d, L, e, ν`. -/
def mult : Fin 6 → ℕ := ![6, 3, 3, 2, 1, 1]
def coloured : Fin 6 → Bool := ![true, true, true, false, false, false]

theorem coloured_channels :
    (∑ i, if coloured i then mult i else 0) = 12 ∧
      (∑ i, if coloured i then 0 else mult i) = 4 ∧ (∑ i, mult i) = 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

def colourLedger : ℝ := 12 * overhead

theorem colour_ledger : colourLedger = 513/43 := by norm_num [colourLedger, overhead]

theorem strong_from_channels :
    (0.11799 : ℝ) < α * footprint / colourLedger ∧ α * footprint / colourLedger < 0.11800 := by
  have h := alpha_footprint_bounds
  rw [colour_ledger]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith [h.1]
  · rw [div_lt_iff₀ (by norm_num)]; linarith [h.2]

theorem in_window : (11.66 : ℝ) < colourLedger ∧ colourLedger < 12.21 := by
  rw [colour_ledger]; constructor <;> norm_num

theorem close_to_paper :
    |α * footprint / colourLedger - (16 * overhead + 1/4) * α| < 0.0001 := by
  have h := alpha_footprint_bounds
  have ha := alpha_bounds
  have hs := strong_from_channels
  have hp1 : (0.11790 : ℝ) < (16 * overhead + 1/4) * α := by
    norm_num [overhead]; nlinarith [ha.1]
  have hp2 : (16 * overhead + 1/4) * α < (0.11791 : ℝ) := by
    norm_num [overhead]; nlinarith [ha.2]
  rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]

theorem weak_not_per_channel : 8 * overhead / footprint < (0.042 : ℝ) := by
  norm_num [overhead, footprint]

end PMConstants.ColourChannels
