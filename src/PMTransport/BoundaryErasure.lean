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

/-! ## Counted boundary annotations

The current controller keeps both circulating streams in its retained
state. The separate disposal annotation has the same address as a
guard decision. Counts here describe tables, before admission of a
boundary itinerary.
-/

abbrev Address := LocalController.Phase × LocalController.Requests × LocalController.Ports
abbrev Policy := Address → Disposition
abbrev RetainingPolicy := Address → {d : Disposition // d ≠ .erase}
abbrev AnnotatedRule := LocalController.EnumeratedRule × Policy
abbrev RetainingRule := LocalController.EnumeratedRule × RetainingPolicy

theorem disposition_count : Fintype.card Disposition = 3 := by decide +kernel

theorem retaining_disposition_count : Fintype.card {d : Disposition // d ≠ .erase} = 2 := by
  decide +kernel

theorem address_count : Fintype.card Address = 688 := by decide +kernel

theorem policy_count : Fintype.card Policy = 3 ^ 688 := by
  rw [Fintype.card_fun, disposition_count, address_count]

theorem retaining_policy_count : Fintype.card RetainingPolicy = 2 ^ 688 := by
  rw [Fintype.card_fun, retaining_disposition_count, address_count]

theorem annotated_rule_count : Fintype.card AnnotatedRule = 8 ^ (4 * 43) * 3 ^ 688 := by
  rw [Fintype.card_prod, LocalController.enumerated_rule_count, policy_count]

theorem retaining_rule_count : Fintype.card RetainingRule = 8 ^ (4 * 43) * 2 ^ 688 := by
  rw [Fintype.card_prod, LocalController.enumerated_rule_count, retaining_policy_count]

/-- A table's erase entries count only at addresses actually visited by
    an exported bit. The itinerary is supplied independently of disposal. -/
def policyCycle (policy : Policy)
    (input : Fin Delta → LocalController.Requests × LocalController.Ports)
    (exports : Fin Delta → Option Bool) : ℕ :=
  cycleErased (fun t => policy (t, input t)) exports

theorem policy_cycle_counts_booked_exports (policy : Policy)
    (input : Fin Delta → LocalController.Requests × LocalController.Ports)
    (exports : Fin Delta → Option Bool) :
    policyCycle policy input exports =
      (Finset.univ.filter fun t => policy (t, input t) = .erase ∧ (exports t).isSome).card := by
  simp [policyCycle, cycleErased, erasedBits, Finset.sum_boole]

theorem policy_cycle_empty (policy : Policy)
    (input : Fin Delta → LocalController.Requests × LocalController.Ports) :
    policyCycle policy input (fun _ => none) = 0 := no_export_cycle _


/-! ## Closed ring and exported open train -/

def ringBoundaryStep {n : ℕ} (either : Bool) (s : RingReceiver.State n) (d : Disposition) :
    RingReceiver.State n × Option Delivery :=
  step (RingReceiver.tick n either) s none d

theorem ring_boundary_step {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (d : Disposition) :
    ringBoundaryStep either s d = (RingReceiver.tick n either s, none) := rfl

/-- The certified ring has no exported bit at any tick. Its original
    receiver flag account is a different observable. -/
theorem ring_cycle_erasure (d : Fin Delta → Disposition) :
    cycleErased d (fun _ => none) = 0 ∧ tollRate (cycleErased d (fun _ => none)) = 0 :=
  ⟨no_export_cycle d, by rw [no_export_cycle]; simp [tollRate]⟩

/-- The certified closed ring has no boundary erasure, so its erasure
    survival weights leave a supplied prior unchanged after normalization.
    This says nothing about how that prior was prepared. -/
theorem ring_erasure_survivor_eq {H : Type*} [Fintype H]
    (prior : H → ℝ) (β : ℝ) (d : H → Fin Delta → Disposition) (i : H) :
    PersistenceMechanics.Selection.survivor prior β
      (fun j => (cycleErased (d j) (fun _ => none) : ℝ)) i =
      prior i / ∑ j, prior j := by
  simp [PersistenceMechanics.Selection.survivor, no_export_cycle]

/-- A circulating record cannot simply be declared disposable. Holding
    the clock, controllers and every live slot fixed, a different
    upstream record can change the next live output of either rule. -/
theorem ring_live_depends_on_record {n : ℕ} (either : Bool) (x : Fin n) :
    ∃ s t : RingReceiver.State n, s.1 = t.1 ∧ s.2.1 = t.2.1 ∧
      s.2.2.1 = t.2.2.1 ∧
      (∀ i, (s.2.2.2 i).1 = (t.2.2.2 i).1) ∧
      ((RingReceiver.tick n either s).2.2.2 x).1 ≠
        ((RingReceiver.tick n either t).2.2.2 x).1 := by
  let s : RingReceiver.State n :=
    (0, (fun _ => (true, true), (fun _ => false, fun _ => (false, false))))
  let t : RingReceiver.State n := (0, (s.2.1, (s.2.2.1,
    fun i => (false, decide (i = finRotate n x)))))
  refine ⟨s, t, rfl, rfl, rfl, fun _ => rfl, ?_⟩
  rw [RingReceiver.tick_ports, RingReceiver.tick_ports]
  cases either <;> simp [s, t, RingReceiver.arrivals, OpenReferenceFlow.streamShift,
    LocalController.applyGuard, RingReceiver.exchange]

/-- Account for the exported record train after a full block of 43 open
    receiver visits, when these addresses have passed outside the core. -/
def openExports (s : OpenHandoff.State Bool) (d : Fin Delta) : Option Bool :=
  some ((OpenHandoff.run s Delta (-(d.val : ℤ))).2)

theorem open_export_source (s : OpenHandoff.State Bool) (d : Fin Delta) :
    openExports s d = some ((s ((d.val : ℤ) - (Delta : ℤ))).1) :=
  congrArg some (OpenHandoff.export_trace s d.isLt)

def receiverRule (either : Bool) : LocalController.Rule :=
  if either then LocalController.exchangeOnEither else LocalController.exchangeOnBoth

theorem tagged_rule_exports (either : Bool) (s : LocalController.State)
    (h : LocalController.CentreTagged s) (d : Fin Delta) :
    some ((((LocalController.rawTick (receiverRule either))^[Delta]) s).2.2
      (-(d.val : ℤ))).2 = openExports s.2.2 d := by
  have hcompatible : LocalController.OpenCompatible (receiverRule either) := by
    cases either <;> exact fun _ _ => ⟨rfl, rfl⟩
  rw [LocalController.tagged_open_iterate (receiverRule either) hcompatible s h]
  rfl

theorem open_cycle_erase_all (s : OpenHandoff.State Bool) :
    cycleErased (fun _ => .erase) (openExports s) = Delta ∧
      tollRate (cycleErased (fun _ => .erase) (openExports s)) = 1 := by
  have h : cycleErased (fun _ => .erase) (openExports s) = Delta :=
    erase_full_cycle (fun d => (OpenHandoff.run s Delta (-(d.val : ℤ))).2)
  exact ⟨h, by rw [h]; exact full_cycle_rate⟩

/-- Conditional ledger when every exchange sends exactly one disposable
    record to the eraser and bypass sends none. The native guard alone
    does not supply this boundary operation. -/
def exchangeErased (either : Bool) (requests : Fin Delta → LocalController.Requests)
    (record : Fin Delta → Bool) : ℕ :=
  cycleErased (fun _ => .erase)
    (fun d => if RingReceiver.exchange either (requests d) then some (record d) else none)

theorem exchange_erasure_gap (requests : Fin Delta → LocalController.Requests)
    (record : Fin Delta → Bool) :
    exchangeErased true requests record =
      exchangeErased false requests record +
        (Finset.univ.filter fun d => (requests d).1 ≠ (requests d).2).card := by
  have hcount : (Finset.univ.filter fun d => (requests d).1 ≠ (requests d).2).card =
      ∑ d : Fin Delta, if (requests d).1 ≠ (requests d).2 then (1 : ℕ) else 0 :=
    Finset.natCast_card_filter (R := ℕ) (fun d => (requests d).1 ≠ (requests d).2) Finset.univ
  unfold exchangeErased cycleErased
  rw [hcount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rcases h : requests d with ⟨a, b⟩
  cases a <;> cases b <;> simp [RingReceiver.exchange, h]

end PMTransport.BoundaryErasure
