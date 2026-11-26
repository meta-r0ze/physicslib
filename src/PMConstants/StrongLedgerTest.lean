import PMConstants.CertifiedConstants
import PMConstants.Partition

/-!
# Only one integer strong ledger survives

`StiffnessIndices` puts the strong readout, in the channel-weighted units that give the weak
mixing `s = Δ/N_sys`, at `α_s  = α N_sys / L₃`. The paper's own formula needs a non-integer
`L₃ ∈ (11, 12)`. If the strong ledger is a count, as the weak ledger `Δ = 43` is, then:

* `alpha_footprint_bounds`: `1.40771 < α N_sys < 1.40772`.
* `ledger_twelve`: `0.11730 < α N_sys/12 < 0.11731`.
* `ledger_separation`: consecutive integer ledgers are more than `0.0088` apart in the readout,
  so the integer count is sharp against any comparison of that precision.

The count itself is derived: colour links maintain the payload of the channels they act on, and
exactly `12` of the sixteen channels carry colour, so `L₃ = 12η` (`ColourChannels.coloured_channels`,
`colour_ledger`). This module only reads the integer ledger. The comparison with `α_s(M_Z)` is in
`tools/e8p/E8PConstants/PMConstants/StrongLedgerPulls.lean`.

Scope. One premise stays explicit: the scale at which a scale-free ledger equals the running
coupling must be stated (with `ScaleResponse`'s log law, `α_s = 0.11731` corresponds to a scale
about 4% above `M_Z` at one loop with five flavours).
-/

noncomputable section
namespace PMConstants.StrongLedgerTest
open PMConstants CertifiedConstants

def ledgerCoupling (L : ℕ) : ℝ := PMSubstrate.causalCoupling * footprint / L

theorem alpha_footprint_bounds : (1.40771 : ℝ) < PMSubstrate.causalCoupling * footprint ∧ PMSubstrate.causalCoupling * footprint < 1.40772 := by
  have h := alpha_bounds
  norm_num [footprint, overhead]
  constructor <;> nlinarith [h.1, h.2]

theorem ledger_twelve : (0.11730 : ℝ) < ledgerCoupling 12 ∧ ledgerCoupling 12 < 0.11731 := by
  have h := alpha_footprint_bounds
  unfold ledgerCoupling
  push_cast
  constructor <;> linarith [h.1, h.2]

/-- **Consecutive integer ledgers are well separated.** Any two distinct positive integer
ledgers at most `13` apart differ by more than `0.0088` in the readout, so the integer count is
sharp against a comparison of that precision. No measured value enters. -/
theorem ledger_separation (L : ℕ) (hL : 0 < L) (hL13 : L ≤ 12) :
    0.0088 < ledgerCoupling L - ledgerCoupling (L + 1) := by
  have h := alpha_footprint_bounds
  have hpos : (0 : ℝ) < PMSubstrate.causalCoupling * footprint := by linarith [h.1]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLu : (L : ℝ) ≤ 12 := by exact_mod_cast hL13
  have hLp : (0 : ℝ) < (L : ℝ) := by linarith
  have hLp1 : (0 : ℝ) < (L : ℝ) + 1 := by linarith
  unfold ledgerCoupling
  push_cast
  rw [div_sub_div _ _ hLp.ne' hLp1.ne', lt_div_iff₀ (by positivity)]
  nlinarith [h.1, h.2]

end PMConstants.StrongLedgerTest
