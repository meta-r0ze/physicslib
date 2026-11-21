import PMAction.DiagonalReadout
import PMKAutomaton.LocalController
import PMElementaryParticles.RecordPortIdentification

/-!
# The receiver and electric flags share a parent up to normalization

The receiver comparison `LocalController.exchangeFlag` is exactly twice
`CommonResponse.linkFlag` on the identity comparison.  The electric record flag
`DiagonalReadout.flag` is `CommonResponse.stateFlag` of a unit phase
(`CommonResponse.gauge_case`).  Both therefore use the common
`CommonResponse.nsq`/`stateFlag` family, but the receiver flag has a factor-two
normalization relative to the unit phase flag.

This is a relation of flags, not a certification of the EP record-port
identification (gap U).
-/

noncomputable section
namespace PMElementaryParticles.CommonComparator

open PMConstants.PacketGaugeActions
open PMKAutomaton LocalController
open PMAction

/-- Receiver comparison is twice the identity link flag. -/
theorem exchangeFlag_eq_two_linkFlag (guard : Guard) (p : Ports)
    (value : Bool → Fin 2 → ℂ) :
    LocalController.exchangeFlag guard p value =
      if guard p then
        2 * CommonResponse.linkFlag (1 : Matrix (Fin 2) (Fin 2) ℂ)
          (value p.2) (value p.1)
      else 0 := by
  unfold LocalController.exchangeFlag CommonResponse.linkFlag CommonResponse.nsq
  split
  · simp [Matrix.one_mulVec]
    ring
  · simp [Matrix.one_mulVec]

/-- The electric flag is the common state flag of a unit phase. -/
theorem flag_eq_stateFlag (x : ℝ) :
    DiagonalReadout.flag x =
      CommonResponse.stateFlag (InterferenceReadout.phase x) (fun _ => (1 : ℂ)) := by
  rw [CommonResponse.gauge_case]
  rfl

end PMElementaryParticles.CommonComparator
