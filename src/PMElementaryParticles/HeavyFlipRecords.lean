import PMElementaryParticles.EventRequirements
import PMElementaryParticles.HeavyFlipControl
import PMTransport.Machine.CoherentRefresh

/-!
# Both-wall hypercharge records on the heavy flip

An auxiliary-only readout driven by hypercharge cannot deterministically recover the
quark doublet bit from a persisting massive label. Both inputs have the same active
charge, with weight one half. This applies to arbitrary comparison schedules sharing
the same record preparation and interacting only through packet hypercharge.

The full and lepton-only comparison costs can still be evaluated as expected flag
counts. Their minimum additive cost for a prescribed independent requirement table is
separate from the ability of those comparisons to write a reversible control record.
-/

noncomputable section
namespace PMElementaryParticles.HeavyFlipRecords

open PMAction PMConstants.ChannelOccupancy EventRequirements ProtocolToll Real

/-- The charge used by the diagonal packet transport. -/
abbrev charge (c : PMConstants.PacketGaugeActions.Channels) : ℝ := ((tag c).2.2 : ℝ) / 3

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
  have hq : charge (quarkActive a i) = charge (quarkActive a j) := rfl
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
    norm_num [charge, tag, leptonActive, quarkActive]
  have staticGap : charge electronStatic - charge (downStatic a) = -(4 / 3) := by
    change ((tag (.inr (.inr (.inr 1)))).2.2 : ℝ) / 3 -
      ((tag (.inr (.inl (a, 1)))).2.2 : ℝ) / 3 = _
    norm_num [tag]
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
  simp only [hyperchargeFlag_eq_cos, tag, quarkActive, leptonActive]
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
  linarith [cos_le_one ((if b then π / 2 else 3 * π / 2) * ((tag cA).2.2 : ℝ) / 3),
    cos_le_one ((if b then π / 2 else 3 * π / 2) * ((tag cS).2.2 : ℝ) / 3)]

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

def pairedToll (cA cS : PMConstants.PacketGaugeActions.Channels) : ℝ :=
  massiveFlag (3 * π / 2) cA cS + massiveFlag (π / 2) cA cS

theorem paired_tolls (a : Fin 3) (i j k l : Fin 2) :
    pairedToll (leptonActive i) electronStatic = 3 / 2 ∧
      pairedToll (quarkActive a j) (downStatic a) = (9 - √3) / 8 ∧
      pairedToll (quarkActive a k) (upStatic a) = (7 - √3) / 8 ∧
      pairedToll (leptonActive l) neutrinoStatic = 1 / 2 := by
  obtain ⟨he, hd, hu, hn⟩ := full_massive a i j k l
  obtain ⟨he', hd', hu', hn'⟩ := quarter_massive a i j k l
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pairedToll, he, hd, hu, hn, he', hd', hu', hn'] <;> ring

/-- The two-visit flag budget has the charged ladder if placed on the heavy flip. -/
theorem paired_ladder (a : Fin 3) (i j k : Fin 2) :
    let s cA cS := TollAmplitude.wireAmplitude (pairedToll cA cS)
    s (leptonActive i) electronStatic < s (quarkActive a j) (downStatic a) ∧
      s (quarkActive a j) (downStatic a) < s (quarkActive a k) (upStatic a) := by
  obtain ⟨he, hd, hu, -⟩ := paired_tolls a i j k 0
  dsimp only
  rw [TollAmplitude.wireAmplitude_lt_iff, TollAmplitude.wireAmplitude_lt_iff, he, hd, hu]
  constructor <;> linarith [Real.sqrt_nonneg 3]

theorem paired_gap_ratio (a : Fin 3) (i j k : Fin 2) :
    let Te := pairedToll (leptonActive i) electronStatic
    let Td := pairedToll (quarkActive a j) (downStatic a)
    let Tu := pairedToll (quarkActive a k) (upStatic a)
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

def orbitRecordToll (c : PMConstants.PacketGaugeActions.Channels) : ℝ :=
  orbitBitPrice c false + orbitBitPrice c true

theorem orbit_record_tolls (a : Fin 3) :
    orbitRecordToll electronStatic = 2 ∧ orbitRecordToll (downStatic a) = 1 ∧
      orbitRecordToll (upStatic a) = 0 ∧ orbitRecordToll neutrinoStatic = 1 := by
  obtain ⟨he, hd, hu, hn⟩ := HeavyFlipControl.static_record_codes a
  change HeavyFlipControl.labelRecord electronStatic = (true, true) at he
  change HeavyFlipControl.labelRecord neutrinoStatic = (true, false) at hn
  simp [orbitRecordToll, orbit_bit_price, he, show HeavyFlipControl.labelRecord (downStatic a) = _ from hd,
    show HeavyFlipControl.labelRecord (upStatic a) = _ from hu, hn]
  norm_num

theorem orbit_record_ladder (a : Fin 3) :
    let s c := TollAmplitude.wireAmplitude (orbitRecordToll c)
    s electronStatic < s (downStatic a) ∧ s (downStatic a) < s (upStatic a) := by
  obtain ⟨he, hd, hu, -⟩ := orbit_record_tolls a
  dsimp only
  rw [TollAmplitude.wireAmplitude_lt_iff, TollAmplitude.wireAmplitude_lt_iff, he, hd, hu]
  norm_num

end PMElementaryParticles.HeavyFlipRecords
