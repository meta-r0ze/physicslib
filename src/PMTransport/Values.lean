import PMTransport.Interface
import PMTransport.RingReceiver

/-!
# Transport values

The period is a substrate count. The tick bounds, rate ratios and record
thresholds have the premises stated below. See `PREMISES.md`.
-/

noncomputable section
namespace PMTransport.Values

abbrev Delta : ℕ := PMSubstrate.E8Values.Delta

theorem Delta_eq : Delta = 43 := PMSubstrate.E8Values.Delta_eq

/-! ## Serial ticks

Admission and Absolute timing. Count two flips on the direct route and
one on the restoring route, plus six serial half-pulse reflections on
either route. The restoring count is a subtotal before node and record work.
`SplitClassBlindFlip.duration_eq` and `ClassBlindFlip.forwardTimes_total`
give the flip lengths. `RootTransferPhase.half_pulse_word` gives the crossing.
The short witness is `SplitClassBlindFlip.one_tick_budget`. For the long
word, `ClassBlindFlip.certain_quarter_even` gives the whole-tick lower
bound and `certain_tick_duration_attained` gives its witness.
-/

def shortSerialTicks (direct : Bool) (q : ℕ) : ℕ :=
  (if direct then 2 else 1) * (24 * q) + 6 * (2 * q)

def longSerialTicks (direct : Bool) (q : ℕ) : ℕ :=
  (if direct then 2 else 1) * (32 * q) + 6 * (2 * q)

theorem shortSerialTicks_min (direct : Bool) {q : ℕ} (hq : 1 ≤ q) :
    shortSerialTicks direct 1 ≤ shortSerialTicks direct q := by
  cases direct <;> simp [shortSerialTicks] <;> omega

theorem longSerialTicks_min (direct : Bool) {q : ℕ} (hq : 2 ≤ q) :
    longSerialTicks direct 2 ≤ longSerialTicks direct q := by
  cases direct <;> simp [longSerialTicks] <;> omega

theorem shortDirectTicks_eq : shortSerialTicks true 1 = 60 := rfl
theorem longDirectTicks_eq : longSerialTicks true 2 = 152 := rfl
theorem shortRestoringSubtotal_eq : shortSerialTicks false 1 = 36 := rfl
theorem longRestoringSubtotal_eq : longSerialTicks false 2 = 88 := rfl

/-! ## Rate ratios

Admission and Absolute timing. Use the serial crossing and one flip on
the same clock. The duration ratios equal physical `r` only with equal
effective areas and equal conversion factors for the two events.
-/

def shortSerialR : ℝ := 12 / 24
def longSerialR : ℝ := 12 / 32

theorem shortSerialR_eq : shortSerialR = 1 / 2 := by norm_num [shortSerialR]
theorem longSerialR_eq : longSerialR = 3 / 8 := by norm_num [longSerialR]

theorem equal_normalization_rate (long : Bool) (tick q area factor : ℝ)
    (ht : 0 < tick) (hq : 0 < q) (ha : area ≠ 0) (hf : factor ≠ 0) :
    (factor * (area / (((if long then 32 else 24) * q) * tick))) /
        (factor * (area / ((12 * q) * tick))) =
      if long then longSerialR else shortSerialR := by
  rw [PMAction.CertainTransferRate.common_tick_rate_ratio tick _ _ _ _ _ _
    ht (by cases long <;> simp <;> positivity) (by positivity) ha hf,
    div_self hf, div_self ha, one_mul, one_mul]
  cases long <;> simp [shortSerialR, longSerialR] <;> field_simp

/-! ## Record thresholds

Admission and Registration tariff. These values use a common uniform
population and unit output flags. The balanced reset value also pays
a separate, fresh-zero receiver comparison for each of two independently
encoded bits. `OpenHandoff.balanced_basis_repair_flag` gives half the
marked bit flag. The packet event counts are certified downstream in
`WireReferenceCost.record_event_counts`.
-/

def outputFlagThreshold (full probeVacancy : Bool) : ℝ :=
  (12 - (if full && probeVacancy then 4 else 3)) / (if full then 16 else 15)

def balancedResetThreshold (full probeVacancy : Bool) : ℝ :=
  (3 / 2) * outputFlagThreshold full probeVacancy

theorem outputFlagThreshold_eq (full probeVacancy : Bool) :
    outputFlagThreshold full probeVacancy =
      if full then (if probeVacancy then 1 / 2 else 9 / 16) else 3 / 5 := by
  cases full <;> cases probeVacancy <;> norm_num [outputFlagThreshold]

theorem balancedResetThreshold_eq (full probeVacancy : Bool) :
    balancedResetThreshold full probeVacancy =
      if full then (if probeVacancy then 3 / 4 else 27 / 32) else 9 / 10 := by
  rw [balancedResetThreshold, outputFlagThreshold_eq]
  cases full <;> cases probeVacancy <;> norm_num

/-! ## Mixed receiver registration rate

D supplies the booked visits. This rate is for site zero on the
certified mixed-basis ring trace. It prices only the specified
comparison at unit registration Toll. The retained ring exports
nothing. A physical comparison still needs O, D and K.
-/

def mixedReceiverRate (either : Bool) (booked : Fin Delta → Bool) : ℝ :=
  (∑ t : Fin Delta, if booked t then
    RingReceiver.receiverFlag either ((RingReceiver.tick 3 either)^[t.val]
      RingReceiver.mixedBasisRing) 0 else 0) / (Delta : ℝ)

theorem mixedReceiverRate_and (booked : Fin Delta → Bool) :
    mixedReceiverRate false booked = 0 := by
  simp [mixedReceiverRate, RingReceiver.mixed_ring_iterate_flag]

theorem mixedReceiverRate_or (booked : Fin Delta → Bool) :
    mixedReceiverRate true booked =
      ((Finset.univ.filter fun t => booked t = true).card : ℝ) / (Delta : ℝ) := by
  unfold mixedReceiverRate
  congr 1
  simp_rw [RingReceiver.mixed_ring_iterate_flag, ite_true]
  rw [Finset.sum_boole]

/-- The other booked work includes any erasure rate on an extended
trace. The total comparison is conditional on those same rate units. -/
theorem mixed_and_cheaper_iff (booked : Fin Delta → Bool) (otherAnd otherOr : ℝ) :
    mixedReceiverRate false booked + otherAnd < mixedReceiverRate true booked + otherOr ↔
      otherAnd - otherOr < ((Finset.univ.filter fun t => booked t = true).card : ℝ) /
        (Delta : ℝ) := by
  rw [mixedReceiverRate_and, mixedReceiverRate_or]
  constructor <;> intro h <;> linarith

/-- At positive hazard, the mixed-trace preference uses the same
explicit work difference and the same booked visits. -/
theorem mixed_and_survives_iff (β : ℝ) (hβ : 0 < β)
    (booked : Fin Delta → Bool) (otherAnd otherOr : ℝ) :
    Real.exp (-β * (mixedReceiverRate true booked + otherOr)) <
      Real.exp (-β * (mixedReceiverRate false booked + otherAnd)) ↔
        otherAnd - otherOr < ((Finset.univ.filter fun t => booked t = true).card : ℝ) /
          (Delta : ℝ) := by
  rw [(PMAction.PersistenceSelection.survival_strictAnti β hβ).lt_iff_gt]
  exact mixed_and_cheaper_iff booked otherAnd otherOr

/-- B supplies the colour-minus-lepton erased bits per input.
The balanced comparison threshold is reproduced only at the
stated erasure difference, with the same booked output flags. -/
theorem erasure_reset_matches_balanced_iff (full probeVacancy : Bool)
    (erasureDifference : ℝ) :
    outputFlagThreshold full probeVacancy - erasureDifference =
      balancedResetThreshold full probeVacancy ↔
        erasureDifference = -(outputFlagThreshold full probeVacancy) / 2 := by
  unfold balancedResetThreshold
  constructor <;> intro h <;> linarith

/-- The two certified placements of a closed non-idle root excursion.
The Boolean indexes an example, with no physical placement selected. -/
def excursionSlots (shifted : Bool) : Fin Delta × Fin Delta :=
  if shifted then (1, 2) else (0, 1)

theorem excursionSlots_boundaries (shifted : Bool) :
    PMAction.CarrierReferenceCycle.boundaries
      (fun t => decide (t = (excursionSlots shifted).2)) =
        {(excursionSlots shifted).1, (excursionSlots shifted).2} := by
  cases shifted <;> decide +kernel

theorem mixedReceiverRate_all_booked (either : Bool) :
    mixedReceiverRate either (fun _ => true) = if either then 1 else 0 := by
  cases either
  · exact mixedReceiverRate_and _
  · rw [mixedReceiverRate_or]
    norm_num [Delta_eq]

end PMTransport.Values
