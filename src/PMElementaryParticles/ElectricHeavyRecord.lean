import PMElementaryParticles.HeavyFlipRecords
import PMConstants.ReferenceRestoration
import PMKAutomaton.Interface

/-!
# Two exact record visits from the carriers' electric charge

The first visit measures the parity of `3Q`. Given that bit, the second
compares the charge against the quark with the same doublet position.
Both use the same electric charge, that of the carriers (`ChargeProtocols.Q`, `bl/2 + t3`). The phase separations and their
principal times follow from the charge spectrum. This supplies a comparison
contract, with a branch encoded on a moved root pair, subject to admission
of the controlled transport and preparation of the seed bank.
-/

noncomputable section
namespace PMElementaryParticles.ElectricHeavyRecord

open PMConstants.PacketGaugeActions HeavyFlipControl ControlledGluedRegister
open PMAction Real Matrix

abbrev q (c : Channels) : ℝ := (ChargeProtocols.Q c).re

theorem charge_from_bits (c : Channels) :
    q c = (if (labelRecord c).1 then 0 else 2 / 3) -
      (if (labelRecord c).2 then 1 else 0) := by
  simp only [q, ChargeProtocols.Q_eval]
  rcases c with ⟨a, i⟩ | ⟨a, i⟩ | i | i <;> fin_cases i <;>
    norm_num [labelRecord, labelIndex] <;> omega

/-- The second reference has the first measured position. Choosing colour
or lepton fixes which output branch registers a sector comparison. -/
def sectorDifference (colourReference : Bool) (c : Channels) : ℝ :=
  q c + (if (labelRecord c).2 then 1 else 0) -
    (if colourReference then 2 / 3 else 0)

theorem colour_difference (c : Channels) :
    sectorDifference true c = if (labelRecord c).1 then -(2 / 3) else 0 := by
  rw [sectorDifference, charge_from_bits]
  simp
  split <;> ring

theorem lepton_difference (c : Channels) :
    sectorDifference false c = if (labelRecord c).1 then 0 else 2 / 3 := by
  rw [sectorDifference, charge_from_bits]
  simp

theorem phase_position (c : Channels) :
    DiagonalReadout.flag (3 * π * q c) = if (labelRecord c).2 then 1 else 0 := by
  rw [charge_from_bits]
  rcases labelRecord c with ⟨sector, position⟩
  cases sector <;> cases position
  · change DiagonalReadout.flag (3 * π * ((2 / 3 : ℝ) - 0)) = 0
    rw [show 3 * π * ((2 / 3 : ℝ) - 0) = 2 * π by ring]
    simp [DiagonalReadout.flag]
  · change DiagonalReadout.flag (3 * π * ((2 / 3 : ℝ) - 1)) = 1
    rw [show 3 * π * ((2 / 3 : ℝ) - 1) = -π by ring, DiagonalReadout.flag_neg,
      DiagonalReadout.flag_pi]
  · simp
  · change DiagonalReadout.flag (3 * π * ((0 : ℝ) - 1)) = 1
    rw [show 3 * π * ((0 : ℝ) - 1) = -(2 * π + π) by ring, DiagonalReadout.flag_neg]
    norm_num [DiagonalReadout.flag, cos_add]

theorem phase_sector (c : Channels) :
    DiagonalReadout.flag (3 * π / 2 * sectorDifference true c) =
      if (labelRecord c).1 then 1 else 0 := by
  rw [colour_difference]
  split
  · rw [show 3 * π / 2 * -(2 / 3) = -π by ring, DiagonalReadout.flag_neg,
      DiagonalReadout.flag_pi]
  · rw [mul_zero, DiagonalReadout.flag_zero]

theorem phase_sector_lepton_reference (c : Channels) :
    DiagonalReadout.flag (3 * π / 2 * sectorDifference false c) =
      if (labelRecord c).1 then 0 else 1 := by
  rw [lepton_difference]
  split
  · rw [mul_zero, DiagonalReadout.flag_zero]
  · rw [show 3 * π / 2 * (2 / 3) = π by ring, DiagonalReadout.flag_pi]

/-- A certain binary flag needs at least a half turn of nonnegative phase. -/
private theorem phase_at_least_pi {x : ℝ} (h0 : 0 ≤ x) (h : DiagonalReadout.flag x = 1) :
    π ≤ x := by
  by_contra hn
  have hc := cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl (lt_of_not_ge hn)
  rw [cos_pi] at hc
  unfold DiagonalReadout.flag at h
  linarith

/-- The down charge fixes the least nonnegative time for the first visit. -/
theorem position_time_minimal (a : Fin 3) {t : ℝ} (h0 : 0 ≤ t)
    (h : DiagonalReadout.flag (t * q (ProtocolFlagCosts.downStatic a)) = 1) : 3 * π ≤ t := by
  have hd : q (ProtocolFlagCosts.downStatic a) = -(1 / 3) := by
    norm_num [q, ProtocolFlagCosts.downStatic, ChargeProtocols.Q_eval]
  rw [hd, mul_neg, DiagonalReadout.flag_neg] at h
  have ht := phase_at_least_pi (by positivity) h
  linarith

/-- The electron-to-down charge contrast fixes the least nonnegative time
of the colour-referenced second visit. -/
theorem sector_time_minimal {t : ℝ} (h0 : 0 ≤ t)
    (h : DiagonalReadout.flag (t * sectorDifference true ProtocolFlagCosts.electronStatic) = 1) :
    3 * π / 2 ≤ t := by
  have hd : sectorDifference true ProtocolFlagCosts.electronStatic = -(2 / 3) := by
    rw [colour_difference]
    change (if true then -(2 / 3 : ℝ) else 0) = _
    simp
  rw [hd, mul_neg, DiagonalReadout.flag_neg] at h
  have ht := phase_at_least_pi (by positivity) h
  linarith

/-- The position and sector readouts act identically on the wall partners. -/
theorem same_wall_pair (c : Channels) :
    q (opposite c) = q c ∧ ∀ b, sectorDifference b (opposite c) = sectorDifference b c := by
  have hq : q (opposite c) = q c := congrArg Complex.re (opposite_charge c)
  exact ⟨hq, fun b => by simp only [sectorDifference, hq, record_opposite]⟩

/-- The exact charge-comparison flag ledger equals the signed-axis bit ledger. -/
theorem colour_reference_toll (c : Channels) :
    DiagonalReadout.flag (3 * π * q c) +
      DiagonalReadout.flag (3 * π / 2 * sectorDifference true c) =
      HeavyFlipRecords.orbitWriterFlagSum c := by
  rw [phase_position, phase_sector, HeavyFlipRecords.orbitWriterFlagSum,
    HeavyFlipRecords.orbit_bit_price, HeavyFlipRecords.orbit_bit_price]
  simp [add_comm]

/-- The position flag is the same orbit bit under either reference.
    Colour reads the sector bit and lepton reads its complement. -/
theorem reference_flags_from_orbit_bits (c : Channels) :
    DiagonalReadout.flag (3 * π * q c) = HeavyFlipRecords.orbitBitPrice c true ∧
      DiagonalReadout.flag (3 * π / 2 * sectorDifference true c) =
        HeavyFlipRecords.orbitBitPrice c false ∧
      DiagonalReadout.flag (3 * π / 2 * sectorDifference false c) =
        1 - HeavyFlipRecords.orbitBitPrice c false := by
  rw [phase_position, phase_sector, phase_sector_lepton_reference,
    HeavyFlipRecords.orbit_bit_price c true, HeavyFlipRecords.orbit_bit_price c false]
  cases (labelRecord c).1 <;> norm_num

/-- Swapping the sector reference swaps its charged polarity. Exact readout
and least phase duration coexist with an electron/down order reversal. -/
theorem lepton_reference_toll (a : Fin 3) :
    let T c := DiagonalReadout.flag (3 * π * q c) +
      DiagonalReadout.flag (3 * π / 2 * sectorDifference false c)
    T ProtocolFlagCosts.electronStatic = 1 ∧ T (ProtocolFlagCosts.downStatic a) = 2 ∧
      T (ProtocolFlagCosts.upStatic a) = 1 ∧ T ProtocolFlagCosts.neutrinoStatic = 0 := by
  obtain ⟨he, hd, hu, hn⟩ := static_record_codes a
  change labelRecord ProtocolFlagCosts.electronStatic = (true, true) at he
  change labelRecord ProtocolFlagCosts.neutrinoStatic = (true, false) at hn
  dsimp only
  simp only [phase_position, phase_sector_lepton_reference, he, hn,
    show labelRecord (ProtocolFlagCosts.downStatic a) = _ from hd,
    show labelRecord (ProtocolFlagCosts.upStatic a) = _ from hu]
  norm_num

/-- A quarter pulse prepares a balanced branch in every actual root orbit
with a moved seed. The overall phase is retained. -/
theorem quarter_prepares (x : Fin 3) (a : CarrierEvents.Carrier x) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1 / 2) :
    let e := CarrierEvents.reflect x
    RootTransferPhase.phase e p (RootTransferPhase.quarterTime p) *ᵥ Pi.single a 1 =
      RootBranchEncoding.embed e a ![(1 - Complex.I) / 2, (1 + Complex.I) / 2] := by
  let e := CarrierEvents.reflect x
  have hinv := CarrierEvents.reflection_involutive x
  have hq : RootTransferPhase.gap p * RootTransferPhase.quarterTime p = π / 2 := by
    unfold RootTransferPhase.quarterTime
    field_simp [(RootTransferPhase.gap_positive p hp hp').ne']
  have he : Complex.exp (-(π / 2 : ℝ) * Complex.I) = -Complex.I := by
    rw [← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  dsimp only
  rw [RootTransferPhase.phase_formula e hinv, hq, he]
  rw [InvolutionSpectral.plus, InvolutionSpectral.minus, add_mulVec, smul_mulVec,
    smul_mulVec, smul_mulVec, add_mulVec, sub_mulVec, one_mulVec,
    RootTransferAccounting.basis_move e hinv, RootBranchEncoding.embed]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  module

/-- An exact flag identifies the signed complex phase, not only its real part. -/
theorem exact_phase (x : ℝ) (b : Bool) (h : DiagonalReadout.flag x = if b then 1 else 0) :
    Complex.exp ((x : ℂ) * Complex.I) = if b then -1 else 1 := by
  have hc : cos x = if b then -1 else 1 := by
    unfold DiagonalReadout.flag at h
    cases b <;> simp_all <;> linarith
  have hs : sin x = 0 := by
    have ht := sin_sq_add_cos_sq x
    rw [hc] at ht
    cases b <;> norm_num at ht <;> nlinarith
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hs, hc]
  cases b <;> simp

/-- The two exact charge comparisons use the actual signs of their
complex kicks, so they can drive the root-orbit writer coherently. -/
theorem packet_kick_phases (c : Channels) :
    Complex.exp ((↑(3 * π * q c : ℝ) : ℂ) * Complex.I) =
        (if (labelRecord c).2 then -1 else 1) ∧
      Complex.exp ((↑(3 * π / 2 * sectorDifference true c : ℝ) : ℂ) * Complex.I) =
        (if (labelRecord c).1 then -1 else 1) :=
  ⟨exact_phase _ _ (phase_position c), exact_phase _ _ (phase_sector c)⟩

/-- Evolution of the encoded two-carrier branch by the spectral phase. -/
private theorem branch_pulse {n : Type*} [Fintype n] [DecidableEq n] (e : Equiv.Perm n)
    (he : Function.Involutive e) (a : n) (z : ℂ) (v : Fin 2 → ℂ) :
    (InvolutionComparison.phase (e.permMatrix ℂ) z) *ᵥ RootBranchEncoding.embed e a v =
      RootBranchEncoding.embed e a
        ![((1 + z) / 2) * v 0 + ((1 - z) / 2) * v 1,
          ((1 - z) / 2) * v 0 + ((1 + z) / 2) * v 1] := by
  rw [InvolutionComparison.phase, InvolutionSpectral.plus, InvolutionSpectral.minus,
    add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, add_mulVec, sub_mulVec,
    one_mulVec, RootBranchEncoding.root_action e he]
  simp only [RootBranchEncoding.embed, RootBranchEncoding.swap, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  module

/-- The forward inverse of a quarter pulse has spectral phase `i` and
uses three positive quarter-times on the very same root. -/
theorem inverse_quarter_forward {n : Type*} [Fintype n] [DecidableEq n] (e : Equiv.Perm n)
    (he : Function.Involutive e) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    RootTransferPhase.phase e p (3 * RootTransferPhase.quarterTime p) =
      InvolutionComparison.phase (e.permMatrix ℂ) Complex.I := by
  have hq : RootTransferPhase.gap p * (3 * RootTransferPhase.quarterTime p) =
      3 * π / 2 := by
    unfold RootTransferPhase.quarterTime
    field_simp [(RootTransferPhase.gap_positive p hp hp').ne']
  have he' : Complex.exp (-(3 * π / 2 : ℝ) * Complex.I) = Complex.I := by
    rw [← Complex.ofReal_neg,
      show -(3 * π / 2) = π / 2 - 2 * π by ring, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    have hi : Complex.exp ((↑(π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp
    rw [hi]
    push_cast
    rw [show (2 * (π : ℂ)) * Complex.I = 2 * π * Complex.I by rfl, Complex.exp_two_pi_mul_I]
    simp
  rw [RootTransferPhase.phase_formula e he, hq, he', InvolutionComparison.phase]

/-- Apply the admitted signed kick to the second branch only. -/
def branchKick {n : Type*} [DecidableEq n] (e : Equiv.Perm n) (a : n) (b : Bool) :
    Matrix n n ℂ :=
  diagonal (fun i => if i = e a ∧ b = true then -1 else 1)

private theorem branch_kick {n : Type*} [Fintype n] [DecidableEq n] (e : Equiv.Perm n)
    (a : n) (ha : e a ≠ a) (b : Bool) (v : Fin 2 → ℂ) :
    branchKick e a b *ᵥ RootBranchEncoding.embed e a v =
      RootBranchEncoding.embed e a ![v 0, if b then -(v 1) else v 1] := by
  ext i
  rw [branchKick, mulVec_diagonal]
  by_cases h : i = a
  · subst i
    cases b <;> simp [RootBranchEncoding.embed, Ne.symm ha]
  · by_cases h' : i = e a
    · subst i
      cases b <;> simp_all [RootBranchEncoding.embed]
    · cases b <;> simp [RootBranchEncoding.embed, h, h']

/-- One exact electric kick between the actual branch pulses writes the
bit. The marked record keeps its physical phase `-i`. -/
theorem root_writer (x : Fin 3) (a : CarrierEvents.Carrier x) (ha : CarrierEvents.reflect x a ≠ a)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) (b : Bool) :
    let e := CarrierEvents.reflect x
    let t := RootTransferPhase.quarterTime p
    RootTransferPhase.phase e p (3 * t) *ᵥ
        (branchKick e a b *ᵥ (RootTransferPhase.phase e p t *ᵥ Pi.single a 1)) =
      RootBranchEncoding.embed e a (if b then ![0, -Complex.I] else ![1, 0]) := by
  dsimp only
  rw [quarter_prepares x a p hp hp',
    branch_kick _ a ha, inverse_quarter_forward _ (CarrierEvents.reflection_involutive x) p hp hp',
    branch_pulse _ (CarrierEvents.reflection_involutive x)]
  congr 1
  cases b <;> ext j <;> fin_cases j <;>
    simp <;> ring_nf <;> norm_num [Complex.I_sq]

/-- Per-factor flag accounting compares successive branch states. -/
private def stepFlag (before after : Fin 2 → ℂ) : ℝ :=
  CommonResponse.nsq (before - after) / 4

/-- The same step flag is measured on the occupied root carrier space. -/
theorem embedded_step_flag {n : Type*} [Fintype n] [DecidableEq n] (e : Equiv.Perm n)
    (a : n) (ha : e a ≠ a) (before after : Fin 2 → ℂ) :
    CommonResponse.nsq (RootBranchEncoding.embed e a before -
      RootBranchEncoding.embed e a after) / 4 = stepFlag before after := by
  have h : RootBranchEncoding.embed e a before - RootBranchEncoding.embed e a after =
      RootBranchEncoding.embed e a (before - after) := by
    simp only [RootBranchEncoding.embed, Pi.sub_apply]
    module
  rw [h, RootBranchEncoding.population e a ha]
  rfl

/-- With one registration per factor flag, the preparation and return
each cost `¼`. The signed kick costs half its exported-bit flag because
only the second orthogonal branch receives it. -/
theorem pulse_flags (b : Bool) :
    let seed : Fin 2 → ℂ := ![1, 0]
    let prepared : Fin 2 → ℂ := ![(1 - Complex.I) / 2, (1 + Complex.I) / 2]
    let kicked : Fin 2 → ℂ := ![(1 - Complex.I) / 2,
      if b then -(1 + Complex.I) / 2 else (1 + Complex.I) / 2]
    let output : Fin 2 → ℂ := if b then ![0, -Complex.I] else ![1, 0]
    stepFlag seed prepared = 1 / 4 ∧
      stepFlag prepared kicked = (if b then 1 / 2 else 0) ∧
      stepFlag kicked output = 1 / 4 := by
  cases b <;> norm_num [stepFlag, LinkExpansion.nsq_eq, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]

/-- The two exact bit writers give this conditional factor-flag ledger,
before physical control, seed, synchronization and export costs. -/
theorem two_bit_factor_toll (c : Channels) :
    (1 / 2 + (if (labelRecord c).1 then 1 / 2 else 0)) +
      (1 / 2 + (if (labelRecord c).2 then 1 / 2 else 0)) =
      1 + HeavyFlipRecords.orbitWriterFlagSum c / 2 := by
  rw [HeavyFlipRecords.orbitWriterFlagSum, HeavyFlipRecords.orbit_bit_price,
    HeavyFlipRecords.orbit_bit_price]
  rcases labelRecord c with ⟨sector, position⟩
  cases sector <;> cases position <;> norm_num

end PMElementaryParticles.ElectricHeavyRecord
