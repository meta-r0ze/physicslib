import PMConstants.ColourChannels
import PMConstants.WMassTest

/-!
# Conditional comparison of common stored-content weights

`ExclusionLawAudit` left two contracts for maintaining stored content: intensive (a per-cell
density maintained relationally from the reference, giving weight `η = 171/172` per unit) and
extensive (weight `1`). A proposed common contract assigns the same weight `w` to payload and gluon
1-form components stored in the grid registers. The assignment, common operational
workload and physical admissibility require justification. The clock and spatial
rows are treated as the address frame with weight `1` in these formulas.

* `ledgers_share_weight`: hypercharge's payload is `16w` and colour's ledger `12w` with the same
  `w`. The colour fork of `4_B_capacity.tex` is the contract question, not an independent choice.
* Two observables then test the single `w` jointly:
  - `extensive_w_mass`, `extensive_strong`: `w = 1` gives `m_W` in `(80.3882, 80.3926)` GeV and
    `α_s` in `(0.11736, 0.11737)`;
  - the intensive values are `WMassTest.w_window` and `ColourChannels.strong_from_channels`.
* `intensive_preferred`: against the direct `m_W` average `80.3692 ± 0.0133` and
  `α_s = 0.1180 ± 0.0009`, the summed squared pulls are below `1.70` for `w = η` and above `2.5`
  for `w = 1`. Both observables move the same way; the preference is mild (Δχ² ≈ 0.8).
* `economy_selects_intensive` proves only the two numerical cost inequalities
  `16η < 16` and `12η < 12`. It does not prove that the contracts execute the same
  required work, or that either has a complete physically admissible schedule.
  Economy can select between them only after those obligations are established.
  The historical theorem name is retained for compatibility.
-/

noncomputable section
namespace PMConstants.ContentWeight
open PMConstants CertifiedConstants StrongLedgerTest

def footprintW (w : ℝ) : ℝ := 172 + 16 * w + 5
def colourW (w : ℝ) : ℝ := 12 * w

theorem ledgers_share_weight :
    footprintW overhead = footprint ∧ colourW overhead = ColourChannels.colourLedger := by
  constructor
  · unfold footprintW footprint; ring
  · unfold colourW ColourChannels.colourLedger; ring

theorem extensive_w_mass {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    80.3882 < mZ * Real.sqrt (1 - 43 / footprintW 1) ∧
      mZ * Real.sqrt (1 - 43 / footprintW 1) < 80.3926 := by
  have h1 : (0.881590 : ℝ) < Real.sqrt (1 - 43 / footprintW 1) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num [footprintW]
  have h2 : Real.sqrt (1 - 43 / footprintW 1) < 0.881592 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num [footprintW]
  constructor <;> nlinarith [h.1, h.2]

theorem extensive_strong :
    (0.11736 : ℝ) < α * footprintW 1 / colourW 1 ∧ α * footprintW 1 / colourW 1 < 0.11737 := by
  have h := alpha_bounds
  norm_num [footprintW, colourW]
  constructor <;> nlinarith [h.1, h.2]

/-- Squared pull. -/
def chi (m σ x : ℝ) : ℝ := ((x - m) / σ)^2

theorem intensive_preferred {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    chi 80.3692 0.0133 (WMassTest.wMass mZ) +
        chi 0.1180 0.0009 (α * footprint / ColourChannels.colourLedger) < 1.70 ∧
      2.5 < chi 80.3692 0.0133 (mZ * Real.sqrt (1 - 43 / footprintW 1)) +
        chi 0.1180 0.0009 (α * footprintW 1 / colourW 1) := by
  have hw := WMassTest.w_window h
  have hs := ColourChannels.strong_from_channels
  have ew := extensive_w_mass h
  have es := extensive_strong
  unfold chi
  constructor
  · have a1 : ((WMassTest.wMass mZ - 80.3692) / 0.0133)^2 < 1.6901 := by
      rw [div_pow]; rw [div_lt_iff₀ (by norm_num)]; nlinarith [hw.1, hw.2]
    have a2 : ((α * footprint / ColourChannels.colourLedger - 0.1180) / 0.0009)^2 < 0.0099 := by
      rw [div_pow]; rw [div_lt_iff₀ (by norm_num)]; nlinarith [hs.1, hs.2]
    linarith
  · have b1 : (2.04 : ℝ) < ((mZ * Real.sqrt (1 - 43 / footprintW 1) - 80.3692) / 0.0133)^2 := by
      rw [div_pow]; rw [lt_div_iff₀ (by norm_num)]; nlinarith [ew.1, ew.2]
    have b2 : (0.49 : ℝ) < ((α * footprintW 1 / colourW 1 - 0.1180) / 0.0009)^2 := by
      rw [div_pow]; rw [lt_div_iff₀ (by norm_num)]; nlinarith [es.1, es.2]
    linarith

/-- A cost ordering, not a derivation of an operational contract or physical selection. -/
theorem economy_selects_intensive :
    footprintW overhead < footprintW 1 ∧ colourW overhead < colourW 1 := by
  constructor <;> norm_num [footprintW, colourW, overhead]

end PMConstants.ContentWeight
