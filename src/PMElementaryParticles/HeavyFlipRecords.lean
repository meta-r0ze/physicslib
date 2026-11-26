import PMElementaryParticles.EventRequirements
import PMElementaryParticles.HeavyFlipControl
import PMKAutomaton.Interface

/-!
# Both-wall hypercharge records on the heavy flip

An auxiliary-only readout driven by hypercharge cannot deterministically recover the
quark doublet bit from a persisting massive label. Both inputs have the same active
charge, with weight one half. This applies to arbitrary comparison schedules sharing
the same record preparation and interacting only through packet hypercharge.

**Legacy audit status.** The record Toll rows are derived as exact flag
comparisons for the candidate reference record (`writeFlagCount_eq_hamming`), but the
reference choice and the heavy-label weight remain premises/undetermined. The
down geometric mean is conditional on the colour reference and a common bit
price; it is not a persistence-derived mass. The P3 least-Toll reference is
per label (up lepton, down colour, electron lepton, neutrino colour); the
selected Tolls are all 1, so the geometric mean holds only as an equal-Toll
case, not as a universal colour-row statement. Status: conditional/consistent,
not contradicted; the single-reference heavy writer assumption is contradicted
as universal.

The full and lepton-only comparison costs can still be evaluated as expected flag
counts. Their minimum additive cost for a prescribed independent requirement table is
separate from the ability of those comparisons to write a reversible control record.

## Readout audit notes

### Heavy flip and record certificates

`WireReferenceCost.reference_threshold_with_erasure` shifts the
output-flag threshold by the difference in booked writer erasures.
The balanced comparison reset keeps its own conditional thresholds.

<a id="finite-control-of-the-direct-heavy-flip"></a>
<a id="record-comparisons-and-heavy-flip-toll"></a>
<a id="an-electric-charge-record-on-both-walls"></a>
<a id="four-port-electric-record-with-fixed-kicks"></a>
<a id="electric-decoder-on-the-odd-coordinate-bank"></a>
<a id="short-root-decoder-and-serial-frame-bound"></a>
<a id="primitive-flags-of-the-short-electric-decoder"></a>
<a id="electric-kicks-from-the-chiral-register-current"></a>
<a id="triality-preparation-on-the-companion"></a>
<a id="primitive-crossing-activity-and-clock-limits"></a>
<a id="other-heavy-weight-diagnostics"></a>

| Theorem or module | What it proves | Conditions |
| --- | --- | --- |
| `HeavyFlipControl.direct_iff`, `ReferenceClassHop.touches_reference_class`, `no_root_only_direct_address`, `flip_encoded`, `flip_light` | The direct address is zero. Untagged roots alias other addresses. The addressed crossing fixes light inputs. | Chosen reference class and supplied generation address. The reverse uses the inverse word. |
| `record_colour`, `record_opposite`, `write_clean`, `registered_word`, `registered_phase_unitary` (`IndependentRegisters`, `RegisterControl`) | Two bits are preserved across walls and colours. The clean write and guarded exchange are reversible. The phase has coefficient `(1−z)/2` on exchanged endpoints. | Occupied banks, clean record and supplied joint control. |
| `CompanionHeavyFlip.ready_pack`, `run_pack`, `run_twice_pack`; `CoherentGate.tensor_dot`, `unequal_needs_orthogonal` | Ordered companion classes recover the heavy address. The update transfers the companion class and returns after two runs. Overlapping weak outputs need orthogonal records. | Packed companion and retained record. |
| `HeavyFlipRecords.quark_auxiliary_gap`, `no_exact_quark_record`, `electron_down_overlap` | Auxiliary outcome gaps for up and down are at most ½. Electron/down squared overlaps at `3π/2` and `π/2` are 1 and ¼. | Shared auxiliary-only hypercharge control with the massive slots left in place. |
| `full_only_minimum`, `quarter_massive`, `paired_minimum`, `paired_tolls`, `paired_ladder`, `paired_gap_ratio` | Full and lepton-only flag ledgers in order e,d,u,ν are `(¾,¾,¼,¼)` and `(¾,(3−√3)/8,(5−√3)/8,¼)`. Their sum gives the charged ladder and gap ratio `2/(3+√3)`. | The relevant visits are independently required and each state flag is charged. These comparisons do not supply the exact record. |
| `orbit_bit_price`, `orbit_record_minimum`, `orbit_record_tolls`, `orbit_record_ladder`, `down_geometric_mean`, `PMAction.TollAmplitude` | The two exact bit visits cost `(2,1,0,1)` in the stated polarity. Down's amplitude is the geometric mean for any common price per bit registration. | Admitted signed-axis phases, clean branch and a separate requirement for each bit. |
| `ElectricHeavyRecord.electric_generator`, `charge_from_bits`, `position_time_minimal`, `sector_time_minimal`, `same_wall_pair`, `packet_kick_phases`, `root_writer` | The electric charge gives the same record on either wall. The principal phase parameters are `3π` and `3π/2`. A quarter preparation, signed kick and three-quarter inverse write the basis record. | Matching-position reference, moving root orbit and supplied joint coupling. |
| `colour_reference_toll`, `lepton_reference_toll`, `reference_flags_from_orbit_bits`, `embedded_step_flag`, `pulse_flags`, `two_bit_factor_toll` | The electric references share the position flag and complement the sector flag. Their two-bit totals are `(2,1,0,1)` and `(1,2,1,0)`. The exhibited writer's three factor flags give `1 + T_bits/2` for two writes. | Choose either comparison-output flags or the exhibited factor flags as paid registrations. These are distinct ledgers. |
| `ElectricFourPortRecord.phase_codes`, `read_exact`, `decoder_word`, `exposure_eq_flags`, `exposure_tolls`, `forward_tolls`, `forward_no_ladder` | Fixed kicks and a decoder write four orthogonal records. Exposures tie electron and down. The forward logical-factor ledgers put down below electron in amplitude. | Prepared balanced bank and one registration per indicated flag. |
| `ElectricDecoderBoundary.phase_word_not_quarter`, `phase_word_not_decoder`; `ElectricCoordinateDecoder.decoder_unitary`, `decoder_observed`, `decoder_reads`, `prepare_balanced`, `encoded_flag` | Uniform-line permutation phases cannot supply the literal decoder. Odd coordinates realize it and expose the primitive state flags. | Coherent root-phase contract, common rate and supplied seed. |
| `short_observed`, `short_reads`, `record_at_short_port`, `short_unitary`, `short_word_exact`, `short_duration`, `undo_word_exact`, `short_prepares`, `undo_duration`, `fresh_bank_serial_exceeds_clock` | The short decoder writes bit-reversed records. Decode and fresh preparation take 25 and 27 quarter-times. | In serial, a fresh bank exceeds one frame when a quarter-time takes at least one tick. |
| `ElectricPrimitiveFlagCosts.primitive_decoder_flags`, `ledger_observed`, `forward_tolls`, `charged_ladder`, `canonical_tie`, `preparation_flags` | Short decoder plus exposures give `(3,5/2,2,1)`. The canonicalizing swap ties down and up. Inverse preparation adds one flag. | One registration per executed state flag and an occupied clean seed. |
| `ElectricChiralKick.high_observed`, `low_observed`, `kick_on_summand`, `high_unitary`, `high_preserves_occupation`, `two_kicks_from_one_current`, `swapped_exposure_toll`, `total_tolls`, `total_ladder`, `total_toll_wall_pair`, `clean_first_seed_at_rest`, `balanced_bank_leaves_rest` | `PMAction.RegisterInteraction.current` and the swap give the two kicks. Forward Tolls are `(13/4,11/4,5/2,1)`. A balanced bank needs a gapped coordinate and separate carrier. | Supplied current and one registration per executed state flag. |
| `ElectricCompanionBank.triality_observed`, `prepares_companion_bank`, `glued_triality_step`, `guarded_companion_transport`, `companion_transport_observed`, `companion_transport_roots`, `written_port_ready_iff`, `setup_class_flag` | Triality prepares the bank from the predecessor seed. The guard transports it. Only the active neutral written port returns ready. The setup endpoint flags ½. | Occupied odd coordinate-zero seed in the proper class. |
| `ElectricCompanionSetupFlagCosts.short_setup_on_seed_support`, `primitive_setup_flags`, `common_setup_on_seed_support`, `equal_slot_setup_sum` | One root suffices on the active seed and two on the static seed. The mean setup flag budget is 5/8. | The certified seed support and equal wall populations. |
| `HeavyCrossingCost.activity_histogram`, `uniform_cost`, `sign_tie` | Six reflects per carrier give 27 idle, 20 unit and one double displacement across eight amplitudes. The mean charge is `(20 c₁ + c₂)/8`. | Uniform amplitudes for the mean, antipodal weights for the sign tie and supplied prices per displacement. |
| `HeavyFlipNativeBoundary.no_closed_cleaning`, `tick_event_iff`, `idle_and_excursion_counts`, `cycle_closes`; `GappedGluedCrossing.equalClass_iff` | The untagged probe aliases addresses and closed universal cleaning is impossible. Both idle and two-toggle masks close. The gapped crossing shifts generation. | The clocked endpoint needs an address and a ready record. |

[Persistence selection](WireSchedule.lean) enumerates a bounded serial family.
[Packet reference cost](WireSchedule.lean)
derives uniform weights under the full-packet sampling premise and
checks the vacancy contribution. The full-packet bit gap is `−1/2`
per sampled input when the vacancy is probed. The smaller support
and the idle-vacancy rule have separate thresholds. The
[lifecycle comparison](WireSchedule.lean)
adds a conditional half flag for a written-bit reset with a fresh
zero. Actual writer traffic and the difference in remaining paid
work still decide the polarity.

Open premises.

- Supply and renew the occupied seed, admit the joint current, controlled phases and crossing, and schedule the two wall insertions. Retain reset or export in the record trace. See the [clock ledger](../PMKAutomaton/OVERVIEW.md#clock).
- Derive the event and tariff. Choose which visits register, which polarity persists, and how the displacement and preparation prices enter. For a price on the node rather than the direct flip, use `node_toll_raises_heavy`.
- The half-period and node-phase diagnostics suggest competing scores. Their selected cadence and paid visits remain open.

Comparison only. The [down mean diagnostic](../../tools/down_mean_check.py) gives `s_d/√(s_e s_u) ≈ 0.96` and inferred prices `2.04` and `2.13` in the ledger convention. The [heavy Toll diagnostic](../../tools/heavy_toll_targets.py) compares the charged gap ratios, including 1 for the short decoder and ½ for the chiral-current candidate. The [bare detuning scan](../../tools/detuning_bound_check.py) tests the `√(3/2) k` bound. These comparisons supply no scheduling inputs.


-/

noncomputable section
namespace PMElementaryParticles.HeavyFlipRecords

open PMAction PMConstants.ChannelOccupancy EventRequirements ProtocolFlagCosts Real

/-- The charge used by the diagonal packet transport. -/
abbrev charge (c : PMConstants.PacketGaugeActions.Channels) : ℝ := (hyperchargeThirds c : ℝ) / 3

/-- The probability of any auxiliary outcome of a charge-only readout on a massive label.
For fixed slot charge, `accept` can include the entire schedule and its auxiliary decoder. -/
def auxiliaryAcceptance (accept : ℝ → ℝ) (cA cS : PMConstants.PacketGaugeActions.Channels) : ℝ :=
  (accept (charge cA) + accept (charge cS)) / 2

/-- Sharing the active slot's charge puts the quark partners' outcome probabilities
within one half of each other, precluding a perfect binary auxiliary record. -/
theorem quark_auxiliary_gap (accept : ℝ → ℝ) (h : ∀ q, 0 ≤ accept q ∧ accept q ≤ 1)
    (a : Fin 3) (i j : Fin 2) :
    |auxiliaryAcceptance accept (quarkActive a i) (downStatic a) -
      auxiliaryAcceptance accept (quarkActive a j) (upStatic a)| ≤ 1 / 2 := by
  have hq : charge (quarkActive a i) = charge (quarkActive a j) := by
    simp [charge, quarkActive, hyperchargeThirds_apply]
  simp only [auxiliaryAcceptance, hq]
  exact abs_le.mpr ⟨by linarith [(h (charge (downStatic a))).1, (h (charge (upStatic a))).2],
    by linarith [(h (charge (downStatic a))).2, (h (charge (upStatic a))).1]⟩

theorem no_exact_quark_record (accept : ℝ → ℝ) (h : ∀ q, 0 ≤ accept q ∧ accept q ≤ 1)
    (a : Fin 3) (i j : Fin 2) :
    ¬ (auxiliaryAcceptance accept (quarkActive a i) (downStatic a) = 1 ∧
       auxiliaryAcceptance accept (quarkActive a j) (upStatic a) = 0) := by
  rintro ⟨hd, hu⟩
  have hg := quark_auxiliary_gap accept h a i j
  rw [hd, hu] at hg
  norm_num at hg

/-- For a comparison's pure auxiliary states the squared overlap is
`|(1 + exp(i t (q - q')))/2|²`. The final common mixer preserves it. -/
def phaseOverlapSq (t q q' : ℝ) : ℝ := 1 - DiagonalReadout.flag (t * (q - q'))

theorem phase_overlap_formula (t q q' : ℝ) :
    Complex.normSq ((1 + Complex.exp (((t * (q - q') : ℝ) : ℂ) * Complex.I)) / 2) =
      phaseOverlapSq t q q' := by
  rw [Complex.normSq_div, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add]
  norm_num [phaseOverlapSq, DiagonalReadout.flag]
  nlinarith [sin_sq_add_cos_sq (t * (q - q'))]

/-- The full step gives identical states for electron and down within each wall;
the lepton-only step leaves squared overlap `¼` within each wall. -/
theorem electron_down_overlap (a : Fin 3) (i j : Fin 2) :
    let qa := charge (leptonActive i)
    let ra := charge (quarkActive a j)
    let qs := charge electronStatic
    let rs := charge (downStatic a)
    phaseOverlapSq (3 * π / 2) qa ra = 1 ∧ phaseOverlapSq (3 * π / 2) qs rs = 1 ∧
      phaseOverlapSq (π / 2) qa ra = 1 / 4 ∧ phaseOverlapSq (π / 2) qs rs = 1 / 4 := by
  have activeGap : charge (leptonActive i) - charge (quarkActive a j) = -(4 / 3) := by
    norm_num [charge, hyperchargeThirds_apply, leptonActive, quarkActive]
  have staticGap : charge electronStatic - charge (downStatic a) = -(4 / 3) := by
    change (hyperchargeThirds (.inr (.inr (.inr 1))) : ℝ) / 3 -
      (hyperchargeThirds (.inr (.inl (a, 1))) : ℝ) / 3 = _
    norm_num [hyperchargeThirds_apply]
  have hc : cos (2 * (π / 3)) = -1 / 2 := by rw [cos_two_mul, cos_pi_div_three]; norm_num
  dsimp only
  simp only [phaseOverlapSq, activeGap, staticGap, DiagonalReadout.flag,
    show 3 * π / 2 * -(4 / 3) = -(2 * π) by ring, cos_neg, cos_two_pi,
    show π / 2 * -(4 / 3) = -(2 * (π / 3)) by ring, hc]
  norm_num

/-- Active slot flags at the lepton-only comparison, from the packet's charges. -/
theorem active_quarter (a : Fin 3) (i j : Fin 2) :
    hyperchargeFlag (π / 2) (quarkActive a i) = (2 - √3) / 4 ∧
      hyperchargeFlag (π / 2) (leptonActive j) = 1 / 2 := by
  simp only [hyperchargeFlag_eq_cos, hyperchargeThirds_apply, quarkActive, leptonActive]
  push_cast
  constructor
  · rw [show π / 2 * 1 / 3 = π / 6 by ring, cos_pi_div_six]; ring
  · rw [show π / 2 * -3 / 3 = -(π / 2) by ring, cos_neg, cos_pi_div_two]; norm_num

/-- The lepton-only comparison costs averaged over both walls, in order `e,d,u,ν`. -/
theorem quarter_massive (a : Fin 3) (i j k l : Fin 2) :
    massiveFlag (π / 2) (leptonActive i) electronStatic = 3 / 4 ∧
      massiveFlag (π / 2) (quarkActive a j) (downStatic a) = (3 - √3) / 8 ∧
      massiveFlag (π / 2) (quarkActive a k) (upStatic a) = (5 - √3) / 8 ∧
      massiveFlag (π / 2) (leptonActive l) neutrinoStatic = 1 / 4 := by
  obtain ⟨he, hd, hu⟩ := flags_quarter a
  obtain ⟨-, hLi⟩ := active_quarter a 0 i
  obtain ⟨-, hLl⟩ := active_quarter a 0 l
  obtain ⟨hQj, -⟩ := active_quarter a j 0
  obtain ⟨hQk, -⟩ := active_quarter a k 0
  have hn := hyperchargeFlag_static_neutral (π / 2)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [massiveFlag, he, hd, hu, hLi, hLl, hQj, hQk, hn] <;> ring

/-- False indexes the full comparison and true the lepton-only comparison. -/
def comparisonPrice (cA cS : PMConstants.PacketGaugeActions.Channels) (quarter : Bool) : ℝ :=
  massiveFlag (if quarter then π / 2 else 3 * π / 2) cA cS

theorem comparisonPrice_nonneg (cA cS : PMConstants.PacketGaugeActions.Channels) (b : Bool) :
    0 ≤ comparisonPrice cA cS b := by
  unfold comparisonPrice massiveFlag
  rw [hyperchargeFlag_eq_cos, hyperchargeFlag_eq_cos]
  linarith [cos_le_one ((if b then π / 2 else 3 * π / 2) * (hyperchargeThirds cA : ℝ) / 3),
    cos_le_one ((if b then π / 2 else 3 * π / 2) * (hyperchargeThirds cS : ℝ) / 3)]

/-- When only the shared static doublet comparison is required, once suffices under Economy. -/
theorem full_only_minimum (cA cS : PMConstants.PacketGaugeActions.Channels) :
    IsLeast {T | ∃ L : List Bool, RefreshSchedule.admissible {false} L ∧
        RefreshSchedule.cost (comparisonPrice cA cS) L = T}
      (massiveFlag (3 * π / 2) cA cS) := by
  simpa [comparisonPrice] using
    RefreshSchedule.minimal_is_ledger _ (comparisonPrice_nonneg cA cS) ({false} : Finset Bool)

/-- If the two comparisons are independently required, the Economy cost is their sum. -/
theorem paired_minimum (cA cS : PMConstants.PacketGaugeActions.Channels) :
    IsLeast {T | ∃ L : List Bool, CoherentRefresh.Restores L ∧
        RefreshSchedule.cost (comparisonPrice cA cS) L = T}
      (massiveFlag (3 * π / 2) cA cS + massiveFlag (π / 2) cA cS) := by
  simpa [comparisonPrice, Fintype.sum_bool, add_comm] using
    CoherentRefresh.minimum_cost _ (comparisonPrice_nonneg cA cS)

def pairedWallFlagSum (cA cS : PMConstants.PacketGaugeActions.Channels) : ℝ :=
  massiveFlag (3 * π / 2) cA cS + massiveFlag (π / 2) cA cS

theorem paired_tolls (a : Fin 3) (i j k l : Fin 2) :
    pairedWallFlagSum (leptonActive i) electronStatic = 3 / 2 ∧
      pairedWallFlagSum (quarkActive a j) (downStatic a) = (9 - √3) / 8 ∧
      pairedWallFlagSum (quarkActive a k) (upStatic a) = (7 - √3) / 8 ∧
      pairedWallFlagSum (leptonActive l) neutrinoStatic = 1 / 2 := by
  obtain ⟨he, hd, hu, hn⟩ := full_massive a i j k l
  obtain ⟨he', hd', hu', hn'⟩ := quarter_massive a i j k l
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pairedWallFlagSum, he, hd, hu, hn, he', hd', hu', hn'] <;> ring

/-- The two-visit flag budget has the charged ladder if placed on the heavy flip. -/
theorem paired_ladder (a : Fin 3) (i j k : Fin 2) :
    let s cA cS := PersistenceMechanics.EffectiveAction.attenuationWeight 1 (pairedWallFlagSum cA cS)
    s (leptonActive i) electronStatic < s (quarkActive a j) (downStatic a) ∧
      s (quarkActive a j) (downStatic a) < s (quarkActive a k) (upStatic a) := by
  obtain ⟨he, hd, hu, -⟩ := paired_tolls a i j k 0
  dsimp only
  rw [TollAmplitude.wireAmplitude_lt_iff, TollAmplitude.wireAmplitude_lt_iff, he, hd, hu]
  constructor <;> linarith [Real.sqrt_nonneg 3]

theorem paired_gap_ratio (a : Fin 3) (i j k : Fin 2) :
    let Te := pairedWallFlagSum (leptonActive i) electronStatic
    let Td := pairedWallFlagSum (quarkActive a j) (downStatic a)
    let Tu := pairedWallFlagSum (quarkActive a k) (upStatic a)
    (Td - Tu) / (Te - Td) = 2 / (3 + √3) := by
  obtain ⟨he, hd, hu, -⟩ := paired_tolls a i j k 0
  dsimp only
  rw [he, hd, hu, show (9 - √3) / 8 - (7 - √3) / 8 = 1 / 4 by ring,
    show (3 : ℝ) / 2 - (9 - √3) / 8 = (3 + √3) / 8 by ring]
  have h : (3 + √3 : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num

/-! ### Exact orbit-bit comparisons, conditional on access to their diagonal phases -/

/-- The phase comparing one of the signed-axis predicates against a clean bit.
The phase difference is a half turn exactly on the marked part of the register. -/
def orbitBitPhase (c : PMConstants.PacketGaugeActions.Channels) (position : Bool) : ℝ :=
  let r := HeavyFlipControl.labelRecord c
  if (if position then r.2 else r.1) then π else 0

/-- The two-wall flag of this comparison is the mean of the slot flags. -/
def orbitBitPrice (c : PMConstants.PacketGaugeActions.Channels) (b : Bool) : ℝ :=
  (DiagonalReadout.flag (orbitBitPhase c b) +
    DiagonalReadout.flag (orbitBitPhase (ControlledGluedRegister.opposite c) b)) / 2

/-- With the designated record phases both walls write the same bit. -/
theorem orbit_bit_price (c : PMConstants.PacketGaugeActions.Channels) (b : Bool) :
    orbitBitPrice c b = if (if b then (HeavyFlipControl.labelRecord c).2
      else (HeavyFlipControl.labelRecord c).1) then 1 else 0 := by
  unfold orbitBitPrice orbitBitPhase
  rw [HeavyFlipControl.record_opposite]
  split <;> split <;> simp_all [DiagonalReadout.flag_pi]

/-- One comparison for each independent bit gives the least scheduled flag cost. -/
theorem orbit_record_minimum (c : PMConstants.PacketGaugeActions.Channels) :
    IsLeast {T | ∃ L : List Bool, CoherentRefresh.Restores L ∧
        RefreshSchedule.cost (orbitBitPrice c) L = T}
      (orbitBitPrice c false + orbitBitPrice c true) := by
  have h : ∀ b, 0 ≤ orbitBitPrice c b := by
    intro b
    rw [orbit_bit_price]
    split <;> split <;> norm_num
  simpa [Fintype.sum_bool, add_comm] using CoherentRefresh.minimum_cost _ h

def orbitWriterFlagSum (c : PMConstants.PacketGaugeActions.Channels) : ℝ :=
  orbitBitPrice c false + orbitBitPrice c true

theorem orbit_record_tolls (a : Fin 3) :
    orbitWriterFlagSum electronStatic = 2 ∧ orbitWriterFlagSum (downStatic a) = 1 ∧
      orbitWriterFlagSum (upStatic a) = 0 ∧ orbitWriterFlagSum neutrinoStatic = 1 := by
  obtain ⟨he, hd, hu, hn⟩ := HeavyFlipControl.static_record_codes a
  change HeavyFlipControl.labelRecord electronStatic = (true, true) at he
  change HeavyFlipControl.labelRecord neutrinoStatic = (true, false) at hn
  simp [orbitWriterFlagSum, orbit_bit_price, he, show HeavyFlipControl.labelRecord (downStatic a) = _ from hd,
    show HeavyFlipControl.labelRecord (upStatic a) = _ from hu, hn]
  norm_num

theorem orbit_record_ladder (a : Fin 3) :
    let s c := PersistenceMechanics.EffectiveAction.attenuationWeight 1 (orbitWriterFlagSum c)
    s electronStatic < s (downStatic a) ∧ s (downStatic a) < s (upStatic a) := by
  obtain ⟨he, hd, hu, -⟩ := orbit_record_tolls a
  dsimp only
  rw [TollAmplitude.wireAmplitude_lt_iff, TollAmplitude.wireAmplitude_lt_iff, he, hd, hu]
  norm_num

/-- **Down is the geometric mean.** For any price `λ` per registration, the exact two-bit
record gives `s_d² = s_e · s_u`: down shares one bit with the electron and none with up, so its
Toll is the mean of theirs. This holds with no free parameter, before any tariff is fixed. -/
theorem down_geometric_mean (lam : ℝ) (a : Fin 3) :
    let s c := PersistenceMechanics.EffectiveAction.attenuationWeight 1 (lam * orbitWriterFlagSum c)
    s (downStatic a) ^ 2 = s electronStatic * s (upStatic a) := by
  obtain ⟨he, hd, hu, -⟩ := orbit_record_tolls a
  dsimp only
  rw [he, hd, hu]
  simp only [PersistenceMechanics.EffectiveAction.attenuationWeight, one_mul]
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  ring_nf

end PMElementaryParticles.HeavyFlipRecords
