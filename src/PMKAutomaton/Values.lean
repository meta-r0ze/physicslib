import PMKAutomaton.Interface
import PMKAutomaton.RingReceiver
import PMKAutomaton.BoundaryErasure

/-!
# KAutomaton values

The period is a substrate count. The tick bounds, rate ratios and record
thresholds have the premises stated below. See `TODO.md`.

## Interface, clock and admission notes

### Certified clock results

Here `Q = RootTransferPhase.quarterTime p`. The parameter `p` is a root
attempt rate. A certificate in this table holds under the hypotheses in
its theorem.

| Status | Result | Certificate and scope |
| --- | --- | --- |
| Certified | The substrate has 43 phases. The reference can follow a closed excursion with two boundaries, at phases 0 and 1. The idle mask also closes. | `PMSubstrate.E8Values.Delta_eq`, `CarrierReferenceCycle.clock_visits`, `cycle_closes`, `excursion_boundaries`, `idle_cycle_cost`. A moving carrier changes at both excursion boundaries. |
| Certified | In statistical-pair time, `Q = π/(2 gap(p))`, where `gap(p) = −2 log(1−2p)`. The principal reflection takes `2Q`. A serial word of six admitted reflections then takes `12Q`. | `RootTransferPhase.quarterTime`, `quarter_pulse`, `half_pulse`, `half_pulse_word`. The time unit is the one in `heat_matches`. |
| Certified | The 16-pulse class-blind beta word takes `32Q`. For a certain transfer with every pulse tick-aligned, its quarter-time in substrate ticks is a positive even integer. The minimum elapsed time is 64 ticks and is attained in that clock model. A serial six-reflection word on the same clock raises the bound to 88 ticks. | `ClassBlindFlip.forwardTimes_total`, `certain_quarter_even`, `certain_tick_duration_lower`, `certain_tick_duration_attained`, `certain_with_six_reflections_lower`. The 88-tick bound counts one flip, not two. |
| Certified | The shorter word realizes the completed certain beta flip with 12 pulses taking `24Q`. At one tick per quarter-time, one flip and one six-reflection word take 36 elapsed ticks. | `SplitClassBlindFlip.pulse_completed`, `duration_eq`, `one_tick_budget`. The witness exceeds 32 ticks and fits in 43. |
| Certified | The same-generation glued crossing has a six-reflection word. The equal-class gapped crossing uses four swap reflections and two amplitude parity reflections. It shifts T at `g` to F at `g+2`. | `GluedRegister.crossingWord`, `crossing_word_glued`, `crossing_word_pure`; `GappedGluedCrossing.runSwap`, `runGappedCrossing_encode`, `equalClass_iff`, `forward_entry`. These results give words and endpoints. |
| Certified | The clocked pair retains two requests at consecutive slots. A shared request always returns to its input. For equal marginals `p`, the independent endpoint-change weight needs joint true-true weight `p²`. | `ClockedRootTrials.ticks_zero_one`, `ticks_one_two`, `shared_request_returns`, `matches_independent_trial_weight`. The endpoint-change weight on a moving input is `2(p−j)` for joint weight `j`. |
| Certified | Coherent integer samples alias gaps modulo a full turn. Under independent trials and `0 ≤ p < 1/2`, the two-trial weight `w = 2p(1−p)` identifies `p` and `gap(p) = −log(1−2w)`. | `RootClockCalibration.phase_alias_iff`, `integer_samples_agree`, `ambiguous_exchange_clock`, `trial_weight_inj`, `gap_from_trials`. A calibrated statistical readout or a principal-range witness can distinguish the aliases. |
| Certified | If a statistical pair occupies two coherent substrate ticks, the generator per tick is `G/2`. In that convention the elapsed quarter-time is `π/gap(p)` substrate ticks. | `ClockedRootTrials.heat_after_two_ticks`, `phase_in_ticks`, `exchange_in_ticks_iff`, `principal_weight_in_ticks`. The correspondence of the physical operations is a separate premise. |
| Certified | A common tick cancels from the flip-to-crossing rate ratio. | `CertainTransferRate.common_tick_rate_ratio`. The formula still uses both pulse areas, coefficient conversions and durations. |

### Periods per route

These bounds describe the supplied serial words and named layouts. The retired EP restoring-capacity mass route used some of these schedules. The clock certificates remain conditional on the stated word and clock.

Count elapsed serial ticks, with carry across periods allowed. For a
block total of `B` whole ticks, a frame-aligned start and exclusive
use of the elapsed clock require at least `⌈B/43⌉` periods. A start at
phase `h` with `0 ≤ h < 43` touches at least `⌈(h+B)/43⌉` periods
when `B>0`. Gaps and guards can increase either bound.

The table uses one gapped crossing and serial whole-tick beta words.
The direct route uses one word on each wall. For the two restoring
routes the node performs the F insertion. `L₁,L₂` stand for the
whole-tick budgets of their entry, dwell and exit, if admitted. All
records, setup, optional fixed-clock reservations and reference renewal
are additional. Each entry is a base budget at the respective minimum
permitted quarter-time.

| Route | With the short word at `q=1` | With the 16-pulse word at `q=2` | Can the full route fit in one 43-tick period? |
| --- | --- | --- | --- |
| Direct `g=0` | `24+12+24 = 60`, at least 2 periods | `64+24+64 = 152`, at least 4 periods | Excluded for this serial two-word implementation, for electron, up and down. |
| Enter the reference class, `g=1` | `36+L₁`. At least 2 periods if node and added work together exceed 7 ticks. | `88+L₁`, at least 3 periods | The short word leaves at most 7 elapsed ticks for the node and all additional work. The long word excludes one period. |
| Leave the reference class, `g=2` | `36+L₂`, with the same 7-tick available budget | `88+L₂`, at least 3 periods | The same exclusions apply. Admittance symmetry establishes no equality of `L₁` and `L₂`. |

If the cycle also executes a separate class-changing crossing, add
`12q`. The direct totals then become 72 and 176, requiring at least
2 and 5 elapsed periods. The restoring subtotals then become 48 and 112
before either node duration, so the short-word one-period option is also
excluded. If an implementation adds a separate beta word at F on a
restoring route, it pays that word's duration as well.

| Logical work if the event is required in the period | Electron | Up | Down |
| --- | --- | --- | --- |
| Charged-current doublet bit | One full or lepton-only visit | One full visit | One full visit |
| Heavy fresh record on the direct address | Two bit visits | Two bit visits | Two bit visits |
| Charged-offset projector at the static vector address | Two matched tests | Two matched tests | Two matched tests |

Timing for those visits and for their reset is still open. The logical
counts come from the slot table. A zero flag on a label does not remove
the corresponding visit from an execution that applies the comparison.
If a fresh inverse-decoder/forward-decoder record is required serially on
the direct route, it adds `52q`. Even with one crossing the base totals
become 112 ticks at `q=1` and 256 at `q=2`, before kicks and reuse.
This gives lower bounds of 3 and 6 periods for that particular record
choice, equally for all three charged protocols.

Under the additional active-slot rule, every serial base budget in the
route table exceeds 32, even the 36-tick short restoring subtotal.
With 11 idle phases and no adjacent idles, the cyclic active mask has
11 nonempty runs. The longest contains at most `32−10 = 22` ticks.
Thus an uninterrupted 24-tick flip cannot stay in active slots on
such a mask, even across the period boundary. A scheduler could allow
idle gaps between primitive pulses if it proves the state is held.
Counts alone would leave the alignment of those pulses open.

If the wall flips can run concurrently, two short 24-tick flips followed
or preceded by one 12-tick crossing have a 36-tick elapsed budget.
That arithmetic does not admit a parallel update. Requiring the
gapped crossing between successive operations on one amplitude instead
precludes overlapping those operations. The library leaves the
physical choice between these executions open. It derives neither a
minimum full-route period count nor a protocol-dependent one.

### Flip-to-crossing rate

Let `A_f,A_y` be the effective pulse areas and `c_f,c_y` the conversions
from pulse rates to Hamiltonian coefficients. Let `d_f,d_y` be the
durations of the individual flip and crossing. With one common tick,
`CertainTransferRate.common_tick_rate_ratio` gives

```text
r = K_f / |y| = (c_f / c_y)(A_f / A_y)(d_y / d_f).
```

In the serial half-pulse execution of either six-reflection crossing,
`d_y = 12q`. The supplied flip durations are `32q` and `24q`. Thus the
conditional duration ratios are `3/8` and `1/2`, respectively. They
give `r` itself if both complete events have equal effective areas and
coefficient conversions. The denominator here is the duration of one
flip. The two-wall cycle budget, record overhead and elapsed time
between firings measure different quantities. Assigning the same area
or duration law to a node-mediated insertion would need its own
derivation. So the current results give conditional ratios and leave
the physical `r` open.

### Comparison only

The recorded first-row wall-leakage diagnostic prefers
`r ≲ 0.07–0.12` with its stated spectral and readout assumptions. The
explored duration options span `1/8 ≤ r ≤ 1/2`. The two conditional
six-reflection ratios above are above the preferred range under equal
normalization. Neither number selects a pulse, a clock, or a record.
See [first-row wall leakage](../PMFlavor/TODO.md#first-row-wall-leakage)
and the [EP readout comparison](../PMElementaryParticles/OVERVIEW.md#charged-density-and-wall-leakage).

### Per-instance rates

Use the substrate phase as the time unit here. These are bounds of the
specified encodings. T still decides elapsed pulse time, sharing and
parallel instances. G and O govern which opportunities are used.

| Part | Per tick and per period | Scope or open rate |
| --- | --- | --- |
| Clock | One phase advance. Visits 43 phases before closing. | `CarrierReferenceCycle.clock_visits`, `clock_closes` and `PMSubstrate.E8Values.Delta_eq`. Physical frequency is T. |
| Node registers | Two output stream slots per site step. | `TwoSiteHandoff.step_trace` and `LocalController.radius_one`. Separate bank writes and simultaneous jobs are G/J. |
| Controller | One receiver decision per site and phase, at most 43 exchanges per period. | `Components.line_receiver_phaseLoad_le`. `ring_receiver_phaseLoad` is exact for fixed requests. Retained trial probes have a separate budget. |
| Root and selector pulses | One possible fire at each trial slot, at most two in its period. | `Components.trial_phaseLoad`, `trial_phaseLoad_le`. Other pulse words need T and G. |
| Receiver | Two arrivals and at most one exchange per site and tick. One displaced record per visit on the supplied open exchange line. | `LocalController.receiver_realisation`, `OpenHandoff.receiver_trace`, `Components.line_receiver_phaseLoad_le`. The encoded open line has 43 visit slots per period. |
| Links | One adjacent hop per stream per step. Each ring output reads one of its two adjacent source sites. | `Components.ring_source_neighbour`, `RingReceiver.port_step_source`, `OpenHandoff.address_step`. The chain of physical 16-slot hops has no joint clock assignment (T/G). |
| Carrier and payload | One source edge per output of the supplied native hop. | `NativePacketUpdate.native_local`. No number of these hops per substrate tick follows (T/L). |
| Reference and preparation | One ready record supplied per exact open visit. | `OpenHandoff.receiver_trace`, `basis_population_required`. Preparation and renewal cadence is Q/T. |
| Readout | The specified ring receiver returns one flag of size at most one per site step. | `Components.ring_flag_le_one`. Other detector counts require D and T. |
| Record path | One FIFO output and one incoming packet accepted per FIFO step, with the record bank shifted. | `RecordTransport.tick_fifo`, `Components.fifo_tick_ports`. FIFO steps per physical tick are T. |
| Boundary | At most one booked exported bit erased per port per tick, and at most 43 per port per period. | `Components.erased_bits_le_one`, `cycle_erased_le_period`. Actual exports and disposition are B. |
| Maintenance | A specified job uses one root event. | `RootMaintenance.event_is_root`. Jobs fitting simultaneously or per period are J/T. |
| EP endpoint | Logical comparisons per candidate write or insertion. | [Clock requirements](OVERVIEW.md#clock). Clock placements and admitted consumer visits are T/U. |

### Margin in matching units

| Encoded reserve | Capacity and maximum load | Worst-case margin |
| --- | --- | --- |
| Clock slots left by the isolated trials | 43 phases, at most two fires, both attainable | 41 unused trial slots. `Components.trial_slot_margin` and `trial_slot_margin_attained`. Shared capacity remains T/J. |
| Controller and receiver exchange opportunities | 43 opportunities and 43 possible exchanges for each rule | Zero unused opportunities at maximum load. `Components.ring_exchange_full_load`. This counts operations, even on equal values. |
| Specified comparison flag | One unit and an attained unit flag for the OR basis witness | Zero headroom in flag units in this case. `Components.ring_flag_margin_attained`. This is independent of booking. |
| Boundary per binary export port | 43 opportunities and 43 possible erased bits | Zero unused slots at maximum load. `Components.erasure_margin_attained`. The retained ring uses zero and leaves the entire accounting capacity unused. |

Each pair uses the same unit. A carrier count does not bound the number
of occupied jobs or the number of pulses per tick. The two stream outputs
and FIFO arity describe slots rather than occupancy. A ready reference
requires supply. The remaining applicable margin entries require the inputs shown above. A physical reserve cannot be assigned from those slot counts.
-/

noncomputable section
namespace PMKAutomaton.Values

export PMSubstrate.E8Values (Delta Delta_eq)

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

def mixedReceiverFlagAt (either : Bool) (t : Fin Delta) : ℝ :=
  RingReceiver.receiverFlag either ((RingReceiver.tick 3 either)^[t.val]
    RingReceiver.mixedBasisRing) 0

def mixedReceiverRate (either : Bool) (booked : Fin Delta → Bool) : ℝ :=
  (∑ t : Fin Delta, if booked t then mixedReceiverFlagAt either t else 0) / (Delta : ℝ)

theorem mixedReceiverFlagAt_eq (either : Bool) (t : Fin Delta) :
    mixedReceiverFlagAt either t = if either then 1 else 0 := by
  unfold mixedReceiverFlagAt
  exact RingReceiver.mixed_ring_iterate_flag either t.val 0

theorem mixedReceiverRate_and (booked : Fin Delta → Bool) :
    mixedReceiverRate false booked = 0 := by
  simp [mixedReceiverRate, mixedReceiverFlagAt_eq]

theorem mixedReceiverRate_or (booked : Fin Delta → Bool) :
    mixedReceiverRate true booked =
      ((Finset.univ.filter fun t => booked t = true).card : ℝ) / (Delta : ℝ) := by
  unfold mixedReceiverRate
  congr 1
  simp_rw [mixedReceiverFlagAt_eq, ite_true]
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

end PMKAutomaton.Values
