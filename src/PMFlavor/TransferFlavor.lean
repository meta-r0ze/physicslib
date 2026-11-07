import PersistenceMechanics.InformationTransfer
import PMFlavor.BreakingPhase
import PMFlavor.MixingMatrix

/-! **Experimental/candidate module.**

# Flavor as information transfer

CKM is boundary conduction, PMNS is capacity promotion, and the broken link is a
coordinate jump.  The mixing overlap is the transfer amplitude ledger.
-/

noncomputable section
namespace PMFlavor.TransferFlavor

open PersistenceMechanics.InformationTransfer
open PMFlavor.BreakingWall

/-- CKM transfer channel: adjacent, interface-limited. -/
def ckmTransfer (phase cost capacityRequired margin : ℝ) : TransferChannel :=
  { mode := .boundaryConduction
    phase := phase
    cost := cost
    capacityRequired := capacityRequired
    margin := margin }

/-- PMNS transfer channel: capacity promotion. -/
def pmnsTransfer (phase cost capacityRequired margin : ℝ) : TransferChannel :=
  { mode := .capacityPromotion
    phase := phase
    cost := cost
    capacityRequired := capacityRequired
    margin := margin }

/-- Broken-link transfer: non-adjacent coordinate jump. -/
def brokenLinkTransfer (w : BreakingPhase) : TransferChannel :=
  { mode := .coordinateJump
    phase := w.delta
    cost := w.epsilon
    capacityRequired := 1
    margin := 1 }

theorem ckmTransfer_mode (phase cost cap margin : ℝ) :
    (ckmTransfer phase cost cap margin).mode = .boundaryConduction := rfl

theorem pmnsTransfer_mode (phase cost cap margin : ℝ) :
    (pmnsTransfer phase cost cap margin).mode = .capacityPromotion := rfl

theorem brokenLinkTransfer_mode (w : BreakingPhase) :
    (brokenLinkTransfer w).mode = .coordinateJump := rfl

theorem pmnsTransfer_expands (phase cost cap margin : ℝ) :
    (pmnsTransfer phase cost cap margin).mode.expandsCapacity = true := rfl

theorem brokenLinkTransfer_not_adjacent (w : BreakingPhase) :
    (brokenLinkTransfer w).mode.adjacent = false := rfl

/-- Mixing overlap amplitude in the protected-state sector. -/
def mixingOverlapAmplitude (ε : ℝ) : ℂ :=
  PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti
    (![1, (PMFlavor.MixingMatrix.rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ)

theorem mixingOverlapAmplitude_eq (ε : ℝ) :
    mixingOverlapAmplitude ε =
      PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti
        (![1, (PMFlavor.MixingMatrix.rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) := rfl

end PMFlavor.TransferFlavor
