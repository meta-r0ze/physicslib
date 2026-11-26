import PMAction.CoherentComparisonRepair
import PMAction.DiagonalReadout
import PMElementaryParticles.CommonComparator
import PMKAutomaton.Machine.CoherentGate

/-!
# Phase-to-record conversion by the certified comparator

`CoherentComparisonRepair.compare (phase x)` is a certified unitary
(`compare_unitary`).  Applied to the phase pair `(1, e^{ix})` in the two
branch ports, its minus output has probability `DiagonalReadout.flag x` and
its plus output has probability `1 - flag x`.  The two output records are the
orthogonal `.inl`/`.inr` branch ports.  This is the converter needed to pass
from the phase encoding of the electric record to the orthogonal record
encoding of the receiver.

This is a conversion theorem; it does not price the comparator or identify its
ports with the physical writer.
-/

noncomputable section
namespace PMElementaryParticles.PhaseToRecord

open PMAction
open PMKAutomaton
open PMAction.CoherentComparisonRepair
open Matrix

/-- The phase-encoded input: amplitude one in the reference branch, `e^{ix}`
in the transported branch. -/
def phaseInput : Unit ⊕ Unit → ℂ :=
  Sum.elim (fun _ => (1 : ℂ)) (fun _ => 0)

/-- The certified comparator applied to the unit phase. -/
def converter (x : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  CoherentComparisonRepair.compare (InterferenceReadout.phase x)

theorem converter_unitary (x : ℝ) :
    converter x ∈ unitary (Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) :=
  CoherentComparisonRepair.compare_unitary _ (InterferenceReadout.phase_unitary x)

theorem converter_minus (x : ℝ) :
    (converter x *ᵥ phaseInput) (.inr ()) =
      (1 - Complex.exp ((x : ℂ) * Complex.I)) / 2 := by
  unfold converter phaseInput CoherentComparisonRepair.compare
  rw [fromBlocks_mulVec]
  simp [CoherentComparisonRepair.minus, CoherentComparisonRepair.plus,
    InterferenceReadout.phase, Matrix.mulVec, dotProduct]
  ring

theorem converter_plus (x : ℝ) :
    (converter x *ᵥ phaseInput) (.inl ()) =
      (1 + Complex.exp ((x : ℂ) * Complex.I)) / 2 := by
  unfold converter phaseInput CoherentComparisonRepair.compare
  rw [fromBlocks_mulVec]
  simp [CoherentComparisonRepair.minus, CoherentComparisonRepair.plus,
    InterferenceReadout.phase, Matrix.mulVec, dotProduct]
  ring

/-- The mismatch (minus) output probability is exactly the electric flag. -/
theorem minus_probability (x : ℝ) :
    Complex.normSq ((converter x *ᵥ phaseInput) (.inr ())) =
      DiagonalReadout.flag x := by
  rw [converter_minus, Complex.normSq_div, DiagonalReadout.normSq_one_sub_exp]
  norm_num [DiagonalReadout.flag]

/-- Receiver weight on a basis outcome: `exchangeFlag` with the outcome as the
guard and the standard orthogonal basis values. -/
noncomputable def outcomeWeight (flip : Bool) : ℝ :=
  LocalController.exchangeFlag (fun _ => flip) (false, true)
    PMKAutomaton.RingReceiver.basisValue

theorem outcomeWeight_true : outcomeWeight true = 1 := by
  unfold outcomeWeight LocalController.exchangeFlag
  simp [PMKAutomaton.RingReceiver.basisValue, LinkExpansion.nsq_eq,
    Fin.sum_univ_two, Pi.single_apply, Complex.normSq_apply]

theorem outcomeWeight_false : outcomeWeight false = 0 := by
  unfold outcomeWeight LocalController.exchangeFlag
  simp

/-- Expected receiver flag after conversion: minus outcome uses `exchangeFlag`
on the mismatch basis, plus outcome uses `exchangeFlag` on the pass basis. -/
noncomputable def expectedReceiverFlag (x : ℝ) : ℝ :=
  Complex.normSq ((converter x *ᵥ phaseInput) (.inr ())) * outcomeWeight true +
    Complex.normSq ((converter x *ᵥ phaseInput) (.inl ())) * outcomeWeight false

theorem expected_receiver_flag (x : ℝ) :
    expectedReceiverFlag x = DiagonalReadout.flag x := by
  unfold expectedReceiverFlag
  rw [outcomeWeight_true, outcomeWeight_false, minus_probability]
  ring

/-- The two converted outcomes are the orthogonal branch records. -/
def plusRecord : Unit ⊕ Unit → ℂ := fun p => if p = .inl () then 1 else 0
def minusRecord : Unit ⊕ Unit → ℂ := fun p => if p = .inr () then 1 else 0

theorem converted_records_orthogonal :
    plusRecord ⬝ᵥ minusRecord = 0 := by
  simp [plusRecord, minusRecord, dotProduct]

/-- The orthogonal-record hypothesis of `CoherentGate.unequal_needs_orthogonal`
is met by the converted branch records. -/
theorem converted_records_meet_unequal_condition :
    ∃ (r₀ r₁ : Unit ⊕ Unit → ℂ), r₀ ⬝ᵥ r₁ = 0 :=
  ⟨plusRecord, minusRecord, converted_records_orthogonal⟩

/-- The EP writeFlagCount row is the sum of the two converted expected flags. -/
theorem writeFlagCount_eq_expected_conversion (colourReference : Bool)
    (c : PMConstants.PacketGaugeActions.Channels) :
    WireSchedule.writeFlagCount colourReference c =
      expectedReceiverFlag (3 * Real.pi * ElectricHeavyRecord.q c) +
        expectedReceiverFlag
          (3 * Real.pi / 2 * ElectricHeavyRecord.sectorDifference colourReference c) := by
  rw [expected_receiver_flag, expected_receiver_flag]
  rfl

/-- Real orthogonal record basis for the converted branches. -/
def plusRecordReal : Fin 2 → ℝ := ![1, 0]
def minusRecordReal : Fin 2 → ℝ := ![0, 1]

theorem converted_branch_records_unequal (a b : ℝ) (_hab : Real.sin (a - b) ≠ 0) :
    CoherentGate.tensor (CoherentGate.col0 a) plusRecordReal ⬝ᵥ
      CoherentGate.tensor (CoherentGate.col1 b) minusRecordReal = 0 := by
  rw [CoherentGate.tensor_dot]
  have h : plusRecordReal ⬝ᵥ minusRecordReal = 0 := by
    simp [plusRecordReal, minusRecordReal, dotProduct, Fin.sum_univ_two]
  rw [h, mul_zero]

/-! ## Coherent encounter and exact-bit case -/

/-- The certified coherent encounter at a firing site: the comparator acting
on the two stream directions `.inl` (live/pass) and `.inr` (record/flip). -/
def encounter (x : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := converter x

theorem encounter_unitary (x : ℝ) :
    encounter x ∈ unitary (Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) :=
  converter_unitary x

/-- At `x = pi`, the encounter is a full flip: plus amplitude zero, minus
amplitude one (up to sign). -/
theorem exact_bit_flip :
    (encounter Real.pi *ᵥ phaseInput) (.inl ()) = 0 ∧
      (encounter Real.pi *ᵥ phaseInput) (.inr ()) = 1 := by
  constructor
  · change (converter Real.pi *ᵥ phaseInput) (.inl ()) = 0
    rw [converter_plus]
    rw [show Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 by
      rw [Complex.exp_mul_I]; simp]
    norm_num
  · change (converter Real.pi *ᵥ phaseInput) (.inr ()) = 1
    rw [converter_minus]
    rw [show Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 by
      rw [Complex.exp_mul_I]; simp]
    norm_num

end PMElementaryParticles.PhaseToRecord
