import PMConstants.GaugeReadoutWeights
import PMConstants.WMassTest
import PMConstants.GaugePersistenceChoice
import PersistenceMechanics.LawSelection

/-!
# The W mass decides how the gauge ledgers enter the coupling law

`GaugeTraceNormalization` left an open choice. Under a uniform packet readout the trace
indices are weak `2`, colour `2`, hypercharge `10/3`. If the ledgers `43` and `129 + 5 + 16η`
are **raw** refresh weights, the indices multiply them and the weak fraction is
`s_raw = 5547/37777` (`raw_mixing_exact`). If they are **effective**, already index-weighted
stiffness, the fraction is the manuscript's `1849/8295` (`effective_work_matching`).
`GaugePersistenceChoice` showed that raw floors plus maximum throughput select the raw
reading, and that queue persistence alone does not decide.

Two inputs now settle it.

* **The preparation is the selected law.** The framework's Selection Principle
  (`PersistenceMechanics.LawSelection`) keeps the uniform law among candidate preparations of the 16
  packet carriers. Each carrier then has weight `1/16` (`selected_is_uniform`), and its
  response indices are `2/16, 2/16, (10/3)/16` (`selected_indices`): exactly the uniform
  readout behind both readings. A nonuniform preparation that rescues the raw reading
  (`(6,3,6,3,2,2)/73`) is not the selected law.
* **The measured W mass.** With the measured `m_Z`, the raw reading gives
  `84.22 < m_W < 84.24` GeV (`raw_w_window`), more than `289σ` above the direct world average
  `80.3692 ± 0.0133` (`raw_excluded`). The effective reading gives `80.3827 < m_W < 80.38644`,
  between `1.0σ` and `1.3σ` (`WMassTest.pull_world`).

So the ledgers are effective stiffness: each already contains its sector's trace index, and
multiplying by the index again is excluded (`ledgers_are_effective`). Consequently the raw-floor
throughput criterion of `GaugePersistenceChoice` is not the operative selection: it picks the
reading the W mass excludes. This is the same pattern as `VevAccounting`, `GravityAccounting`
and `ScalarAccounting`, where an observable selects the accounting rule.

Remaining obligation: derive the effective ledgers as primitive work, i.e. show why the counted
refreshes `43` and `129 + 5 + 16η` already carry the indices `2` and `10/3` (raw weights
`43/2` and `(3/10)(129 + 5 + 16η)`, `GaugePersistenceChoice.effective_reading_factors`).
The selection premises are those of `PersistenceMechanics.HazardForm`.

`ReferenceCharge` gives the reason: stiffness is read on a reference carrier, not through the
uniformly sampled packet, and the lepton-doublet reference has equal weak and hypercharge
indices, which is the effective reading.
-/

noncomputable section
namespace PMConstants.ReadoutAccounting
open PMConstants GaugeReadoutWeights

/-- Per-carrier weights of the selected preparation. -/
def selectedWeights : RequirementTable.Ty → ℝ := fun _ => 1 / 16

theorem channels_card : Fintype.card PacketGaugeActions.Channels = 16 := by decide

/-- **The selected preparation is uniform on the 16 carriers.** -/
theorem selected_is_uniform (c : PacketGaugeActions.Channels) :
    (PersistenceMechanics.LawSelection.uniform : PacketGaugeActions.Channels → ℝ) c =
      selectedWeights (channelType c) := by
  simp [PersistenceMechanics.LawSelection.uniform, selectedWeights]

/-- Its response indices are the uniform packet indices `2, 2, 10/3`, up to the common `1/16`. -/
theorem selected_indices :
    weakIndex selectedWeights = 2 / 16 ∧ colourIndex selectedWeights = 2 / 16 ∧
      hyperIndex selectedWeights = (10 / 3) / 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [weakIndex, colourIndex, hyperIndex, selectedWeights]

/-- W mass under the raw reading. -/
def rawWMass (mZ : ℝ) : ℝ := mZ * Real.sqrt (1 - 5547 / 37777)

theorem raw_w_window {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    84.22 < rawWMass mZ ∧ rawWMass mZ < 84.24 := by
  have hs1 : (0.92366 : ℝ) < Real.sqrt (1 - 5547 / 37777) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt (1 - 5547 / 37777) < 0.92368 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold rawWMass
  constructor <;> nlinarith [h.1, h.2]

/-- **The raw reading is excluded** by the direct world average. -/
theorem raw_excluded {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    289 < WMassTest.pull 80.3692 0.0133 (rawWMass mZ) := by
  have hw := raw_w_window h
  unfold WMassTest.pull
  rw [lt_div_iff₀ (by norm_num)]; linarith

/-- **The ledgers are effective stiffness.** Under the selected preparation, reading them as raw
weights puts the W mass more than `289σ` off; reading them as effective puts it within `1.3σ`. -/
theorem ledgers_are_effective {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) {c : ℝ} (hc : 0 < c) :
    GaugeTraceNormalization.rawMixing c = 5547 / 37777 ∧
      289 < WMassTest.pull 80.3692 0.0133 (rawWMass mZ) ∧
      WMassTest.pull 80.3692 0.0133 (WMassTest.wMass mZ) < 1.3 ∧
      1.0 < WMassTest.pull 80.3692 0.0133 (WMassTest.wMass mZ) :=
  ⟨GaugeTraceNormalization.raw_mixing_exact hc, raw_excluded h,
    (WMassTest.pull_world h).2, (WMassTest.pull_world h).1⟩

end PMConstants.ReadoutAccounting
