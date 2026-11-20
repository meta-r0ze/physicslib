import PMAction.CoherentComparisonRepair
import PMAction.DiagonalReadout
import PMElementaryParticles.CommonComparator
import PMTransport.Machine.CoherentGate

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

/-- The mismatch (minus) output probability is exactly the electric flag. -/
theorem minus_probability (x : ℝ) :
    Complex.normSq ((converter x *ᵥ phaseInput) (.inr ())) =
      DiagonalReadout.flag x := by
  rw [converter_minus, Complex.normSq_div, DiagonalReadout.normSq_one_sub_exp]
  norm_num [DiagonalReadout.flag]

/-- Expected receiver flag after conversion: the minus port registers one, the
plus port zero. -/
noncomputable def expectedReceiverFlag (x : ℝ) : ℝ :=
  Complex.normSq ((converter x *ᵥ phaseInput) (.inr ())) * 1 +
    Complex.normSq ((converter x *ᵥ phaseInput) (.inl ())) * 0

theorem expected_receiver_flag (x : ℝ) :
    expectedReceiverFlag x = DiagonalReadout.flag x := by
  unfold expectedReceiverFlag
  rw [minus_probability]
  ring

/-- The two converted outcomes are the orthogonal branch records. -/
def plusRecord : Unit ⊕ Unit → ℂ := fun p => if p = .inl () then 1 else 0
def minusRecord : Unit ⊕ Unit → ℂ := fun p => if p = .inr () then 1 else 0

theorem converted_records_orthogonal :
    plusRecord ⬝ᵥ minusRecord = 0 := by
  simp [plusRecord, minusRecord, dotProduct, Fintype.sum_sum_type]

/-- The orthogonal-record hypothesis of `CoherentGate.unequal_needs_orthogonal`
is met by the converted branch records. -/
theorem converted_records_meet_unequal_condition :
    ∃ (r₀ r₁ : Unit ⊕ Unit → ℂ), r₀ ⬝ᵥ r₁ = 0 :=
  ⟨plusRecord, minusRecord, converted_records_orthogonal⟩

/-- The EP bitToll row is the sum of the two converted expected flags. -/
theorem bitToll_eq_expected_conversion (colourReference : Bool)
    (c : PMConstants.PacketGaugeActions.Channels) :
    WireSchedule.bitToll colourReference c =
      expectedReceiverFlag (3 * Real.pi * ElectricHeavyRecord.q c) +
        expectedReceiverFlag
          (3 * Real.pi / 2 * ElectricHeavyRecord.sectorDifference colourReference c) := by
  rw [expected_receiver_flag, expected_receiver_flag]
  rfl

/-- Real orthogonal record basis for the converted branches. -/
def plusRecordReal : Fin 2 → ℝ := ![1, 0]
def minusRecordReal : Fin 2 → ℝ := ![0, 1]

theorem converted_branch_records_unequal (a b : ℝ) (hab : Real.sin (a - b) ≠ 0) :
    CoherentGate.tensor (CoherentGate.col0 a) plusRecordReal ⬝ᵥ
      CoherentGate.tensor (CoherentGate.col1 b) minusRecordReal = 0 := by
  rw [CoherentGate.tensor_dot]
  have h : plusRecordReal ⬝ᵥ minusRecordReal = 0 := by
    simp [plusRecordReal, minusRecordReal, dotProduct, Fin.sum_univ_two]
  rw [h, mul_zero]

end PMElementaryParticles.PhaseToRecord
