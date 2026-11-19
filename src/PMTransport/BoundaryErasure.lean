import PMTransport.RingReceiver
import PMTransport.Machine.ReferenceMaintenance

/-!
# Boundary erasure account

The protected update is a permutation. An exported bit is a separate
input to a disposal operation and cannot feed the next protected update.
In the binary erasure account a designated reset of one exported unknown
bit costs one unit. Routing, reuse and readiness still require their
own realization. The account makes no identification with comparison flags.
-/

namespace PMTransport.BoundaryErasure

open scoped BigOperators
open PMAction

inductive Disposition
  | keep
  | recycle
  | erase
  deriving DecidableEq

instance : Fintype Disposition :=
  ⟨{.keep, .recycle, .erase}, by intro d; cases d <;> simp⟩

inductive Delivery
  | kept (bit : Bool)
  | recycled (bit : Bool)
  | reset (bit : Bool)
  deriving DecidableEq

/-- The ready record is the clean slot of the existing Boolean reference
    encoding. The reference charge is not a function of the old bit. -/
def readyRecord : Bool :=
  (ReferenceMaintenance.prepare (fun _ : Unit => false) ()).2

def deliver (disposition : Disposition) (bit : Bool) : Delivery :=
  match disposition with
  | .keep => .kept bit
  | .recycle => .recycled bit
  | .erase => .reset readyRecord

/-- `some` denotes a supplied bit booked for this boundary operation.
    A bit is charged for erasure only when a reset is executed. -/
def erasedBits (disposition : Disposition) (exported : Option Bool) : ℕ :=
  if disposition = .erase ∧ exported.isSome then 1 else 0

def step {I : Type*} (update : Equiv.Perm I) (identity : I)
    (exported : Option Bool) (disposition : Disposition) : I × Option Delivery :=
  (update identity, exported.map (deliver disposition))

theorem identity_bijective {I : Type*} (update : Equiv.Perm I)
    (exported : I → Option Bool) (disposition : I → Disposition) :
    Function.Bijective (fun i => (step update i (exported i) (disposition i)).1) :=
  update.bijective

theorem kept_bit_injective : Function.Injective (deliver .keep) := by
  intro a b h
  cases h
  rfl

theorem recycled_bit_injective : Function.Injective (deliver .recycle) := by
  intro a b h
  cases h
  rfl

theorem erased_bit_merges (a b : Bool) :
    deliver .erase a = deliver .erase b := rfl

theorem erasure_not_injective : ¬ Function.Injective (deliver .erase) := by
  intro h
  exact Bool.false_ne_true (h (erased_bit_merges false true))

@[simp] theorem no_export_no_erasure (disposition : Disposition) :
    erasedBits disposition none = 0 := by simp [erasedBits]

@[simp] theorem keep_no_erasure (exported : Option Bool) :
    erasedBits .keep exported = 0 := by simp [erasedBits]

@[simp] theorem recycle_no_erasure (exported : Option Bool) :
    erasedBits .recycle exported = 0 := by simp [erasedBits]

@[simp] theorem erasing_pays_one (bit : Bool) :
    erasedBits .erase (some bit) = 1 := rfl

/-- Account for at most one booked export bit per tick at a port. -/
def cycleErased (disposition : Fin Delta → Disposition)
    (exported : Fin Delta → Option Bool) : ℕ :=
  ∑ t, erasedBits (disposition t) (exported t)

/-- Erasure Toll per tick over the substrate period. -/
def tollRate (bits : ℕ) : ℚ := bits / (Delta : ℚ)

theorem no_export_cycle (disposition : Fin Delta → Disposition) :
    cycleErased disposition (fun _ => none) = 0 := by
  simp [cycleErased]

theorem keep_cycle (exported : Fin Delta → Option Bool) :
    cycleErased (fun _ => .keep) exported = 0 := by
  simp [cycleErased]

theorem erase_full_cycle (bits : Fin Delta → Bool) :
    cycleErased (fun _ => .erase) (fun t => some (bits t)) = Delta := by
  simp [cycleErased]

theorem full_cycle_rate : tollRate Delta = 1 := by
  norm_num [tollRate, PMAction.Delta_eq]

end PMTransport.BoundaryErasure
