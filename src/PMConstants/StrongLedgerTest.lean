import PMConstants.CertifiedConstants
import PMConstants.Partition

/-!
# Only one integer strong ledger survives

`StiffnessIndices` puts the strong readout, in the channel-weighted units that give the weak
mixing `s = Δ/N_sys`, at `α_s = α N_sys / L₃`. The paper's own formula needs a non-integer
`L₃ ∈ (11, 12)`. If the strong ledger is a count, as the weak ledger `Δ = 43` is, then:

* `alpha_footprint_bounds`: `1.40771 < α N_sys < 1.40772`.
* `integer_ledger_unique`: among positive integers, `L₃ = 12` is the only one whose readout lies
  within three standard deviations of the comparison value `α_s(M_Z) = 0.1180 ± 0.0009`
  (PDG 2024). Every `L₃ ≤ 11` gives more than `0.1279`; every `L₃ ≥ 13` gives less than `0.1083`.
* `ledger_twelve`: `0.11730 < α N_sys/12 < 0.11731`, a pull between `−0.78` and `−0.77`.

Scope. This makes the integer count falsifiable but does not derive `12`; integers in this
range are about 8% apart, so landing within 3σ of one is not by itself significant. Two
premises stay explicit: the count `L₃ = 12` must come from the substrate's colour refresh, and
the scale at which a scale-free ledger equals the running coupling must be stated (with
`ScaleResponse`'s log law, `α_s = 0.11731` corresponds to a scale about 4% above `M_Z` at one loop with five flavours).
-/

noncomputable section
namespace PMConstants.StrongLedgerTest
open PMConstants CertifiedConstants

def ledgerCoupling (L : ℕ) : ℝ := α * footprint / L

theorem alpha_footprint_bounds : (1.40771 : ℝ) < α * footprint ∧ α * footprint < 1.40772 := by
  have h := alpha_bounds
  norm_num [footprint, overhead]
  constructor <;> nlinarith [h.1, h.2]

theorem ledger_twelve : (0.11730 : ℝ) < ledgerCoupling 12 ∧ ledgerCoupling 12 < 0.11731 := by
  have h := alpha_footprint_bounds
  unfold ledgerCoupling
  push_cast
  constructor <;> linarith [h.1, h.2]

theorem integer_ledger_unique (L : ℕ) (hL : 0 < L) :
    |ledgerCoupling L - 0.1180| < 3 * 0.0009 ↔ L = 12 := by
  have h := alpha_footprint_bounds
  have hpos : (0 : ℝ) < α * footprint := by linarith [h.1]
  constructor
  · intro habs
    rcases lt_trichotomy L 12 with hl | hl | hl
    · exfalso
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hL11 : (L : ℝ) ≤ 11 := by exact_mod_cast (by omega : L ≤ 11)
      have hge : α * footprint / 11 ≤ ledgerCoupling L := by
        unfold ledgerCoupling
        exact div_le_div_of_nonneg_left hpos.le (by linarith) hL11
      have := (abs_lt.mp habs).2
      linarith [h.1]
    · exact hl
    · exfalso
      have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast (by omega : 13 ≤ L)
      have hle : ledgerCoupling L ≤ α * footprint / 13 := by
        unfold ledgerCoupling
        exact div_le_div_of_nonneg_left hpos.le (by norm_num) hL13
      have := (abs_lt.mp habs).1
      linarith [h.2]
  · rintro rfl
    have h12 := ledger_twelve
    rw [abs_lt]
    constructor <;> linarith [h12.1, h12.2]

end PMConstants.StrongLedgerTest
