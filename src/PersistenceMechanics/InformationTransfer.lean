import PersistenceMechanics.EffectiveAction
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Three information-transfer modes

Paper IV's transfer classification, stated substrate-generally:

```
Boundary Conduction : adjacent, continuous, interface-limited
Capacity Promotion  : hierarchical, expands the capacity bound
Coordinate Jump     : non-adjacent, discontinuous, address-space leap
```

A transfer channel carries a phase and a cost; its amplitude and rate use the
same effective-action form as every other PM process.
-/

noncomputable section
namespace PersistenceMechanics.InformationTransfer

open PersistenceMechanics.EffectiveAction

inductive TransferMode
  | boundaryConduction
  | capacityPromotion
  | coordinateJump
  deriving DecidableEq, Repr

def TransferMode.adjacent : TransferMode → Bool
  | .boundaryConduction => true
  | .capacityPromotion => true
  | .coordinateJump => false

def TransferMode.continuous : TransferMode → Bool
  | .boundaryConduction => true
  | .capacityPromotion => false
  | .coordinateJump => false

def TransferMode.expandsCapacity : TransferMode → Bool
  | .boundaryConduction => false
  | .capacityPromotion => true
  | .coordinateJump => false

theorem modes_pairwise_distinct :
    TransferMode.boundaryConduction ≠ .capacityPromotion ∧
    TransferMode.boundaryConduction ≠ .coordinateJump ∧
    TransferMode.capacityPromotion ≠ .coordinateJump := by
  decide

/-- A transfer channel: phase action, cost, required capacity, margin. -/
structure TransferChannel where
  mode : TransferMode
  phase : ℝ
  cost : ℝ
  capacityRequired : ℝ
  margin : ℝ

/-- Transfer amplitude from the shared effective-action form. -/
def TransferChannel.amplitude (β : ℝ) (c : TransferChannel) : ℂ :=
  EffectiveAction.amplitude c.phase β c.cost

/-- Transfer rate. -/
def TransferChannel.rate (β : ℝ) (c : TransferChannel) : ℝ :=
  c.margin * Complex.normSq (c.amplitude β)

/-- A transfer is admissible when capacity suffices. -/
def TransferChannel.admissible (available : ℝ) (c : TransferChannel) : Prop :=
  c.capacityRequired ≤ available

/-- Boundary conduction is interface-limited: it cannot expand capacity. -/
theorem boundaryConduction_not_expanding :
    TransferMode.boundaryConduction.expandsCapacity = false := rfl

/-- Capacity promotion is the only mode that expands the capacity bound. -/
theorem capacityPromotion_expands :
    TransferMode.capacityPromotion.expandsCapacity = true := rfl

end PersistenceMechanics.InformationTransfer
