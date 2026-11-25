import PMAction.CommonResponse
import PMKAutomaton.RestoringExtraction

/-!
# Transported and registered capacity in the ring receiver

Carry scalar capacity on the existing live and record streams. The native
stencil preserves the sum of the stored values, including across a booked
bank exchange. At a registered comparison the arriving values give the
claim at that site and tick. A marker with capacity c over a zero-capacity
reference contributes c at each exact mismatch flag. This is a receiver
account for the supplied program and booking.
-/

noncomputable section

namespace PMKAutomaton.ReceiverCapacity

open PMAction RingReceiver RestoringExtraction
open scoped BigOperators

/-- Apply a capacity readout to each stored value without changing its slot. -/
def capacityPorts {n : ℕ} {V : Type*} (capacity : V → ℝ)
    (ports : OpenReferenceFlow.State (Fin n) V) : OpenReferenceFlow.State (Fin n) ℝ :=
  fun x => (capacity (ports x).1, capacity (ports x).2)

/-- Reading capacity after routing gives the same field as routing the
capacity values themselves. The readout is a map on the retained payload. -/
theorem capacity_ports_step {n : ℕ} {V : Type*} (either : Bool) (requests : RequestsField n)
    (capacity : V → ℝ) (ports : OpenReferenceFlow.State (Fin n) V) :
    capacityPorts capacity (valueStep either requests ports) =
      valueStep either requests (capacityPorts capacity ports) := by
  funext x
  cases h : exchange either (requests x) <;>
    simp [capacityPorts, valueStep, OpenReferenceFlow.streamShift, h]

/-- Capacity held across the live and record slots of a finite receiver. -/
def storedCapacity {n : ℕ} (ports : OpenReferenceFlow.State (Fin n) ℝ) : ℝ :=
  ∑ x, ((ports x).1 + (ports x).2)

/-- The two streams permute their values and a receiver exchange only
reorders the two arrivals at its own site. -/
theorem stored_capacity_step {n : ℕ} (either : Bool) (requests : RequestsField n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) :
    storedCapacity (valueStep either requests ports) = storedCapacity ports := by
  unfold storedCapacity
  calc
    _ = ∑ x : Fin n, ((ports ((finRotate n).symm x)).1 + (ports (finRotate n x)).2) := by
      apply Finset.sum_congr rfl
      intro x _
      cases h : exchange either (requests x) <;>
        simp [valueStep, OpenReferenceFlow.streamShift, h, add_comm]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Equiv.sum_comp (finRotate n).symm (fun x => (ports x).1),
        Equiv.sum_comp (finRotate n) (fun x => (ports x).2)]

theorem stored_capacity_trace {n : ℕ} (either : Bool) (requests : RequestsField n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) (ticks : ℕ) :
    storedCapacity ((valueStep either requests)^[ticks] ports) = storedCapacity ports := by
  induction ticks with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', stored_capacity_step, ih]

/-- Extraction and reload move capacity between the live slot and the
external bank. Their joint total is conserved. -/
theorem stored_capacity_bank {n : ℕ} (site : Fin n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) (bank : ℝ) :
    let swapped := exchangeLive site (ports, bank)
    storedCapacity swapped.1 + swapped.2 = storedCapacity ports + bank := by
  intro swapped
  have hold (x : Fin n) (hx : x ≠ site) : swapped.1 x = ports x := by
    change ((if x = site then bank else (ports x).1), (ports x).2) = ports x
    simp [hx]
  have hsite : swapped.1 site = (bank, (ports site).2) := by
    change ((if site = site then bank else (ports site).1), (ports site).2) = _
    simp
  have hother : (∑ x ∈ Finset.univ.erase site, ((swapped.1 x).1 + (swapped.1 x).2)) =
      ∑ x ∈ Finset.univ.erase site, ((ports x).1 + (ports x).2) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hold x (Finset.mem_erase.mp hx).1]
  unfold storedCapacity
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ site),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ site), hother, hsite]
  change _ + (ports site).1 = _
  ring

/-- Use the capacity on the two arriving slots at every exact receiver
registration. The arrival field and the registration field share the
receiver's stencil. -/
def registeredTick {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) : ℝ :=
  CommonResponse.bookedCapacity Finset.univ
    (fun x => let p := OpenReferenceFlow.streamShift (finRotate n) ports x
              p.1 + p.2)
    (receiverFlag either s)

/-- Capacity registered over the native ticks from the supplied receiver
state and the supplied capacity streams. -/
def registeredTrace {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) (ticks : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ticks,
    registeredTick either ((RingReceiver.tick n either)^[k] s)
      ((valueStep either s.2.1)^[k] ports)

/-- Concatenating two consecutive windows adds their claims. The second
window starts with the actual state and transported values at the join. -/
theorem registered_trace_add {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) (first second : ℕ) :
    registeredTrace either s ports (first + second) =
      registeredTrace either s ports first +
        registeredTrace either ((RingReceiver.tick n either)^[first] s)
          ((valueStep either s.2.1)^[first] ports) second := by
  unfold registeredTrace
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [requests_iterate, ← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm first k]

/-- A returning program has the same capacity bill for a whole cycle
starting at any phase of its execution. -/
theorem registered_cycle_phase_invariant {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (ports : OpenReferenceFlow.State (Fin n) ℝ) (period offset : ℕ)
    (hstate : (RingReceiver.tick n either)^[period] s = s)
    (hports : (valueStep either s.2.1)^[period] ports = ports) :
    registeredTrace either ((RingReceiver.tick n either)^[offset] s)
      ((valueStep either s.2.1)^[offset] ports) period =
        registeredTrace either s ports period := by
  have hprefix := registered_trace_add either s ports offset period
  have hperiod := registered_trace_add either s ports period offset
  rw [hstate, hports, Nat.add_comm period offset, hprefix] at hperiod
  linarith only [hperiod]

theorem registered_tick_lift {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (capacity : ℝ) :
    registeredTick either s (liftPorts 0 capacity s.2.2.2) =
      capacity * ∑ x, receiverFlag either s x := by
  rw [registeredTick, CommonResponse.booked_capacity_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [receiver_flag_eq]
  change ((if (arrivals s.2.2.2 x).1 then capacity else 0) +
    (if (arrivals s.2.2.2 x).2 then capacity else 0)) * _ = _
  cases (arrivals s.2.2.2 x).1 <;>
    cases (arrivals s.2.2.2 x).2 <;>
    cases exchange either (s.2.1 x) <;> simp

theorem registered_trace_lift {n : ℕ} (either : Bool) (s : RingReceiver.State n)
    (capacity : ℝ) (ticks : ℕ) :
    registeredTrace either s (liftPorts 0 capacity s.2.2.2) ticks =
      capacity * ∑ k ∈ Finset.range ticks, ∑ x, receiverFlag either ((RingReceiver.tick n either)^[k] s) x := by
  unfold registeredTrace
  simp_rw [value_trace_lift, registered_tick_lift, Finset.mul_sum]

open RestoringRingHistory

/-- The restoring seed holds exactly one copy of the carried value. -/
theorem restoring_seed_capacity (q : History) (capacity : ℝ) :
    storedCapacity (liftPorts 0 capacity (seed q).2.2.2) = capacity := by
  change (∑ x : Fin Delta,
    ((if decide (x = (42 : Fin Delta)) then capacity else 0) +
      (if false then capacity else 0))) = capacity
  simp

/-- At the successful extraction all stored marker capacity is in the bank. -/
theorem banked_stored_capacity (either : Bool) (q : History)
    (hLive : liveExit either q = true) (capacity : ℝ) :
    let extracted := exchangeLive (42 : Fin Delta)
      ((valueStep either (seed q).2.1)^[2] (liftPorts 0 capacity (seed q).2.2.2), 0)
    storedCapacity extracted.1 = 0 ∧ extracted.2 = capacity := by
  dsimp only
  rw [extract_values either q hLive 0 capacity]
  simp [storedCapacity]

/-- A successful retained marker registers its capacity on every tick
of the first period. -/
theorem closed_restoring_period (either : Bool) (q : History)
    (hLive : liveExit either q = true) (capacity : ℝ) :
    registeredTrace either (seed q) (liftPorts 0 capacity (seed q).2.2.2) Delta =
      capacity * Delta := by
  rw [registered_trace_lift]
  exact congrArg (capacity * ·) (successful_receiver_toll_period either q hLive)

/-- The full closed cycle returns the capacity field and charges every
registration in the complete receiver history, including both visits
when only one switch fires. -/
theorem closed_restoring_cycle (either : Bool) (q : History) (capacity : ℝ) :
    let s := seed q
    let ports := liftPorts 0 capacity s.2.2.2
    (valueStep either s.2.1)^[2 * Delta] ports = ports ∧
      registeredTrace either s ports (2 * Delta) = capacity *
        (if liveExit either q then 86 else if exchange either q.1 || exchange either q.2 then 2 else 0) := by
  dsimp only
  constructor
  · rw [value_trace_lift, seed_returns]
  · rw [registered_trace_lift]
    exact congrArg (capacity * ·) (full_receiver_toll either q)

/-- After the tick-two extraction the ring contributes no more registered
capacity. The separate bank operations have their own booking. -/
theorem banked_restoring_receiver (either : Bool) (q : History)
    (hLive : liveExit either q = true) (capacity : ℝ) (remaining : ℕ) :
    let s := (extract either q).1
    registeredTrace either (seed q) (liftPorts 0 capacity (seed q).2.2.2) 2 +
      registeredTrace either s (liftPorts 0 capacity s.2.2.2) remaining = capacity * 2 := by
  intro s
  rw [registered_trace_lift, registered_trace_lift, ← mul_add]
  exact congrArg (capacity * ·) (extracted_prefix_receiver_toll either q hLive remaining)

end PMKAutomaton.ReceiverCapacity
