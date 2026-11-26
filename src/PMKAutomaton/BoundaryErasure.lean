import PMKAutomaton.RingReceiver
import PMKAutomaton.Machine.ReferenceMaintenance

/-!
# Boundary erasure account

The protected update is a permutation. An exported bit is a separate
input to a disposal operation and cannot feed the next protected update.
In the binary erasure account a designated reset of one exported unknown
bit costs one unit. Routing, reuse and readiness still require their
own realization. The account makes no identification with comparison flags.

## Interface, clock and admission notes

### Boundary erasure

The [audit](OVERVIEW.md#reversibility-boundary) marks the retained results,
boundary claims and counts. `BoundaryErasure.identity_bijective`
keeps the protected update bijective. Keep and recycle preserve
the exported bit. Erasure merges its two values into the clean
record. `erasing_pays_one` counts the reset of a booked binary
record as one unit. The bookable record has already left the
core and cannot feed its next update.

The existing guard tables retain both circulating streams. A
separate disposal annotation at each of their 688 input addresses
gives `8^(4×43) × 3^688` tables, of which
`8^(4×43) × 2^688` contain no erase instruction
(`annotated_rule_count`, `retaining_rule_count`). The difference
counts tables that permit an erase instruction. For a fixed
itinerary with `m` booked export bits at distinct phase addresses,
exactly `choose(m,k) × 2^(m−k) × 3^(688−m)` annotations per core
erase `k` bits in that cycle. Choose the `k` erasing addresses,
fill the other booked addresses with keep or recycle, then fill
the unused addresses. `policy_cycle_counts_booked_exports`
identifies the visits being counted. With no booked exports all
tables have zero erasures per cycle. None of these table counts
assigns a physical itinerary or a different core register partition.

| Model | Status | Erased bits per period | Erasure Toll per tick |
| --- | --- | ---: | ---: |
| Certified closed ring, either rule | Derived. Both streams remain operands and no port exports. | 0 | 0 |
| Tagged open train, either rule, keep or recycle the exported bits | Conditional on that disposition. | 0 | 0 |
| Tagged open train, either rule, erase all booked bits after they leave the core | Conditional on 43 visits and disposal of all 43 bits in the period. | 43 | 1 |
| One booked erasure on each exchange and none on bypass | Conditional on that export law. OR pays one more per mixed-request visit than AND. | OR minus AND is the mixed-visit count | That count divided by 43 |

`ring_live_depends_on_record` rules out using the circulating
record slot itself as the discard port of the certified ring.
`open_export_source` identifies the displaced input at each open
export address. `tagged_rule_exports` gives the same train for
both rules on the tagged receiver. `exchange_erasure_gap` gives
the conditional mixed-visit count. Least erasure Toll selects
neither rule on the certified ring or on the same tagged open
train under common disposal. Those ties hold for any prior.
A mixed-request advantage requires the missing export contract.

### Accounting by operation

`Components.booked_registration_and_erasure_sum` partitions supplied booked unit
registrations by component owner. It equals
`NetCost.expectedCost` on the same events, plus the separately booked
boundary erasures. Each registration must be a single event in that
list. Multiple readers do not prove multiple executed writes. The
identity uses the uniform law on the supplied sample space of
`NetCost`. A nonuniform law still needs its supplied masses and the
weighted accounting rule (`EventAccounting.weighted_linear`).

| Component | Certifiable account | Stage still missing |
| --- | --- | --- |
| Clock | Clock phase and duration bounds. | Price of physically advancing and sharing the clock. |
| Registers | Occupation is conserved under the encoded update. | Cost of a physical read, write or preparation outside the specified counters. |
| Controller | Null receiver flag registration in the retained tick without an attached detector. | Cost of switching or retaining the physical guard. |
| Pulses | `CarrierEvents.uniform_activation` counts a supplied uniform primitive activation. | Primitive tariffs and which complete word is run and paid. |
| Receiver | The branch and flag are computed on the stated arrivals. | Physical flag booking and any separate receiver work. |
| Links | Conditional current and admittance. | Price of the executed crossings and traffic. |
| Carrier | Slot and wall dimensions. | Paid work for the actual carried label and wall. |
| Reference | Exact supplied restoration and conditional preparation/reset flags. | Seed and maintenance price and its reuse at a common visit. |
| Readout | `InBandRootReadout.expected_read_undo_cost` prices the actual two root events on the clean norm-two sample at the supplied unit price. | Selection of that detector and the tariff for other detectors and gates. |
| Records | Logical record preservation and FIFO. | Physical write, hold, export and reuse, plus any reset other than a booked erase. |
| Boundary | One Toll per booked erased bit. Zero on the certified retained ring. | Which physical bits reach the port and their disposition. |
| Maintenance | Minimum supplied job ledger under `RefreshSchedule.minimal_is_ledger`. | Job ownership, shared upkeep and remaining prices. |
| EP | Conditional output flag and balanced reset thresholds. | Booked visits, writer population and the difference in all other work, including any actual erasure reset. |

`NetIndex.index_as_net_transitions` is the substrate's six-term
baseline. The partition identity checks equality to the supplied
`NetCost` event total. There is no identification of these machine
visits and erasures with the baseline provisioning and removed-event
sets. An equality to that global index remains an event-identification
input under K, rather than another rate or scalar tariff.
-/

namespace PMKAutomaton.BoundaryErasure

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
def cycleErased (disposition : Fin PMSubstrate.E8Values.Delta → Disposition)
    (exported : Fin PMSubstrate.E8Values.Delta → Option Bool) : ℕ :=
  ∑ t, erasedBits (disposition t) (exported t)

/-- Erasure Toll per tick over the substrate period. -/
def erasedBitsPerTick (bits : ℕ) : ℚ := bits / (PMSubstrate.E8Values.Delta : ℚ)

theorem no_export_cycle (disposition : Fin PMSubstrate.E8Values.Delta → Disposition) :
    cycleErased disposition (fun _ => none) = 0 := by
  simp [cycleErased]

theorem keep_cycle (exported : Fin PMSubstrate.E8Values.Delta → Option Bool) :
    cycleErased (fun _ => .keep) exported = 0 := by
  simp [cycleErased]

theorem erase_full_cycle (bits : Fin PMSubstrate.E8Values.Delta → Bool) :
    cycleErased (fun _ => .erase) (fun t => some (bits t)) = PMSubstrate.E8Values.Delta := by
  simp [cycleErased]

theorem full_cycle_rate : erasedBitsPerTick PMSubstrate.E8Values.Delta = 1 := by
  norm_num [erasedBitsPerTick, PMSubstrate.E8Values.Delta_eq]

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
    (input : Fin PMSubstrate.E8Values.Delta → LocalController.Requests × LocalController.Ports)
    (exports : Fin PMSubstrate.E8Values.Delta → Option Bool) : ℕ :=
  cycleErased (fun t => policy (t, input t)) exports

theorem policy_cycle_counts_booked_exports (policy : Policy)
    (input : Fin PMSubstrate.E8Values.Delta → LocalController.Requests × LocalController.Ports)
    (exports : Fin PMSubstrate.E8Values.Delta → Option Bool) :
    policyCycle policy input exports =
      (Finset.univ.filter fun t => policy (t, input t) = .erase ∧ (exports t).isSome).card := by
  simp [policyCycle, cycleErased, erasedBits, Finset.sum_boole]

theorem policy_cycle_empty (policy : Policy)
    (input : Fin PMSubstrate.E8Values.Delta → LocalController.Requests × LocalController.Ports) :
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
theorem ring_cycle_erasure (d : Fin PMSubstrate.E8Values.Delta → Disposition) :
    cycleErased d (fun _ => none) = 0 ∧ erasedBitsPerTick (cycleErased d (fun _ => none)) = 0 :=
  ⟨no_export_cycle d, by rw [no_export_cycle]; simp [erasedBitsPerTick]⟩

/-- The certified closed ring has no boundary erasure, so its erasure
    survival weights leave a supplied prior unchanged after normalization.
    This says nothing about how that prior was prepared. -/
theorem ring_erasure_survivor_eq {H : Type*} [Fintype H]
    (prior : H → ℝ) (β : ℝ) (d : H → Fin PMSubstrate.E8Values.Delta → Disposition) (i : H) :
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
def openExports (s : OpenHandoff.State Bool) (d : Fin PMSubstrate.E8Values.Delta) : Option Bool :=
  some ((OpenHandoff.run s PMSubstrate.E8Values.Delta (-(d.val : ℤ))).2)

theorem open_export_source (s : OpenHandoff.State Bool) (d : Fin PMSubstrate.E8Values.Delta) :
    openExports s d = some ((s ((d.val : ℤ) - (PMSubstrate.E8Values.Delta : ℤ))).1) :=
  congrArg some (OpenHandoff.export_trace s d.isLt)

def receiverRule (either : Bool) : LocalController.Rule :=
  if either then LocalController.exchangeOnEither else LocalController.exchangeOnBoth

theorem tagged_rule_exports (either : Bool) (s : LocalController.State)
    (h : LocalController.CentreTagged s) (d : Fin PMSubstrate.E8Values.Delta) :
    some ((((LocalController.rawTick (receiverRule either))^[PMSubstrate.E8Values.Delta]) s).2.2
      (-(d.val : ℤ))).2 = openExports s.2.2 d := by
  have hcompatible : LocalController.OpenCompatible (receiverRule either) := by
    cases either <;> exact fun _ _ => ⟨rfl, rfl⟩
  rw [LocalController.tagged_open_iterate (receiverRule either) hcompatible s h]
  rfl

theorem open_cycle_erase_all (s : OpenHandoff.State Bool) :
    cycleErased (fun _ => .erase) (openExports s) = PMSubstrate.E8Values.Delta ∧
      erasedBitsPerTick (cycleErased (fun _ => .erase) (openExports s)) = 1 := by
  have h : cycleErased (fun _ => .erase) (openExports s) = PMSubstrate.E8Values.Delta :=
    erase_full_cycle (fun d => (OpenHandoff.run s PMSubstrate.E8Values.Delta (-(d.val : ℤ))).2)
  exact ⟨h, by rw [h]; exact full_cycle_rate⟩

/-- Conditional ledger when every exchange sends exactly one disposable
    record to the eraser and bypass sends none. The native guard alone
    does not supply this boundary operation. -/
def exchangeErased (either : Bool) (requests : Fin PMSubstrate.E8Values.Delta → LocalController.Requests)
    (record : Fin PMSubstrate.E8Values.Delta → Bool) : ℕ :=
  cycleErased (fun _ => .erase)
    (fun d => if RingReceiver.exchange either (requests d) then some (record d) else none)

theorem exchange_erasure_gap (requests : Fin PMSubstrate.E8Values.Delta → LocalController.Requests)
    (record : Fin PMSubstrate.E8Values.Delta → Bool) :
    exchangeErased true requests record =
      exchangeErased false requests record +
        (Finset.univ.filter fun d => (requests d).1 ≠ (requests d).2).card := by
  have hcount : (Finset.univ.filter fun d => (requests d).1 ≠ (requests d).2).card =
      ∑ d : Fin PMSubstrate.E8Values.Delta, if (requests d).1 ≠ (requests d).2 then (1 : ℕ) else 0 :=
    Finset.natCast_card_filter (R := ℕ) (fun d => (requests d).1 ≠ (requests d).2) Finset.univ
  unfold exchangeErased cycleErased
  rw [hcount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rcases h : requests d with ⟨a, b⟩
  cases a <;> cases b <;> simp [RingReceiver.exchange, h]

end PMKAutomaton.BoundaryErasure
