import PMElementaryParticles.ProgramCapacity

/-!
# Capacity on the retained occupation of a restoring receiver

The receiver already carries an occupation marker on each stream. Pair
that marker with the typed carrier value it accompanies. The native
stencil transports the pair and the existing basis comparator reads the
marker. The occupied-slot readout counts one unit per marked slot. This
certifies the receiver contribution in slot units on the booked history.
-/

noncomputable section

namespace PMElementaryParticles.RetainedReceiverCapacity

open PMAction PMKAutomaton RingReceiver RestoringRingHistory RestoringExtraction
open IsolatedExcitation OccupiedBankedRestoring GluedRegister ControlledGluedRegister
open GappedGluedCrossing

abbrev CarrierPair := Wt × Wt
abbrev Retained := Bool × CarrierPair

/-- Keep the same Boolean occupation bit that the ring comparator reads. -/
def portsOf (payload reference : CarrierPair) (s : RingReceiver.State Delta) :
    OpenReferenceFlow.State (Fin Delta) Retained :=
  liftPorts (false, reference) (true, payload) s.2.2.2

private theorem arriving_tags (payload reference : CarrierPair) (s : RingReceiver.State Delta)
    (x : Fin Delta) :
    OpenReferenceFlow.streamShift (finRotate Delta) (portsOf payload reference s) x =
      ((if (arrivals s.2.2.2 x).1 then (true, payload) else (false, reference)),
       (if (arrivals s.2.2.2 x).2 then (true, payload) else (false, reference))) := rfl

/-- The typed occupied state follows the same reversible stencil. -/
theorem retained_trace (either : Bool) (s : RingReceiver.State Delta)
    (payload reference : CarrierPair) (ticks : ℕ) :
    (valueStep either s.2.1)^[ticks] (portsOf payload reference s) =
      portsOf payload reference ((RingReceiver.tick Delta either)^[ticks] s) :=
  value_trace_lift either s _ _ ticks

/-- The marked carrier arrives live at entry and on the record stream at
exit. The bank swap retains that same marked carrier. -/
theorem occupied_visits (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) (reference : CarrierPair) :
    let s := chargedSeed g vacuum q
    let payload := restoringPayload g a sign
    let ports := portsOf payload reference s
    let entered := valueStep either s.2.1 ports
    OpenReferenceFlow.streamShift (finRotate Delta) ports 0 =
      ((true, payload), (false, reference)) ∧
    OpenReferenceFlow.streamShift (finRotate Delta) entered 42 =
      ((false, reference), (true, payload)) ∧
    exchangeLive (42 : Fin Delta)
      ((valueStep either s.2.1)^[2] ports, (false, reference)) =
        ((fun _ => ((false, reference), (false, reference))), (true, payload)) := by
  dsimp only
  rw [charged_seed_eq]
  obtain ⟨hentry, hexit⟩ := successful_arrivals either q hLive
  refine ⟨?_, ?_, extract_values either q hLive _ _⟩
  · rw [arriving_tags, hentry]
    rfl
  · have he := retained_trace either (seed q) (restoringPayload g a sign) reference 1
    simp only [Function.iterate_one] at he
    rw [he, arriving_tags, hexit]
    rfl

/-- In the matched address-2 case the retained fields still distinguish
the carrier and reference, even though their carrier projection agrees. -/
theorem matched_address_two_entry (vacuum : VacuumLabel (wallClass 2 false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) :
    let reference := (frame 0 1, frame 0 (signedAxis (a + 2) sign))
    let inputs := OpenReferenceFlow.streamShift (finRotate Delta)
      (portsOf (restoringPayload 2 a sign) reference (chargedSeed 2 vacuum q)) 0
    inputs.1.2 = inputs.2.2 ∧ inputs.1.1 = true ∧ inputs.2.1 = false := by
  dsimp only
  rw [(occupied_visits 2 vacuum a sign either q hLive _).1]
  exact ⟨(address_two_payload_eq_reference_iff _ _ _ _).2 ⟨rfl, rfl⟩, rfl, rfl⟩

/-- The local readout counts the occupied marker in one slot. -/
def occupiedSlots (v : Retained) : ℝ := if v.1 then 1 else 0

private theorem capacity_ports_of (value : Bool → ℝ) (payload reference : CarrierPair)
    (s : RingReceiver.State Delta) :
    ReceiverCapacity.capacityPorts (fun v : Retained => value v.1 - value false)
        (portsOf payload reference s) =
      liftPorts 0 (value true - value false) s.2.2.2 := by
  funext x
  rcases h : s.2.2.2 x with ⟨live, record⟩
  cases live <;> cases record <;>
    simp [ReceiverCapacity.capacityPorts, portsOf, liftPorts, h]

/-- The occupied input contributes one unit at each of the two registered
visits, for either address and any supplied prepared carrier coordinates. -/
theorem occupied_visit_claims (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) (reference : CarrierPair) :
    let s := chargedSeed g vacuum q
    let payload := restoringPayload g a sign
    let entry := OpenReferenceFlow.streamShift (finRotate Delta) (portsOf payload reference s) 0
    let exit := OpenReferenceFlow.streamShift (finRotate Delta)
      (valueStep either s.2.1 (portsOf payload reference s)) 42
    CommonResponse.responseCost (occupiedSlots entry.1 + occupiedSlots entry.2) 1
        (receiverFlag either s 0) = 1 ∧
      CommonResponse.responseCost (occupiedSlots exit.1 + occupiedSlots exit.2) 1
        (receiverFlag either (RingReceiver.tick Delta either s) 42) = 1 := by
  dsimp only
  obtain ⟨hentry, hexit, _⟩ := occupied_visits g vacuum a sign either q hLive reference
  rw [hentry, hexit, charged_seed_eq]
  obtain ⟨hl, hr⟩ := successful_arrivals either q hLive
  have hctrl := hLive
  rw [live_exit, Bool.and_eq_true] at hctrl
  rw [receiver_flag_eq, receiver_flag_eq, hl, hr]
  change CommonResponse.responseCost (1 + 0) 1
      (if exchange either q.1 = true ∧ true ≠ false then 1 else 0) = 1 ∧
    CommonResponse.responseCost (0 + 1) 1
      (if exchange either q.2 = true ∧ false ≠ true then 1 else 0) = 1
  norm_num [CommonResponse.responseCost, hctrl.1, hctrl.2]

/-- Any common capacity assigned solely by the retained occupation bit
gives the same banked receiver claim at both restoring addresses. -/
theorem tag_receiver_claim (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) (reference : CarrierPair) (value : Bool → ℝ) :
    let s := chargedSeed g vacuum q
    let banked := (extract either q).1
    let ports := fun state => ReceiverCapacity.capacityPorts
      (fun v : Retained => value v.1 - value false)
      (portsOf (restoringPayload g a sign) reference state)
    ReceiverCapacity.registeredTrace either s (ports s) 2 +
      ReceiverCapacity.registeredTrace either banked (ports banked) (2 * Delta - 2) =
        (value true - value false) * 2 := by
  dsimp only
  rw [charged_seed_eq, capacity_ports_of, capacity_ports_of]
  exact ReceiverCapacity.banked_restoring_receiver either q hLive _ _

/-- The occupied-slot readout counts two over the whole banked receiver. -/
theorem occupied_receiver_claim (g : Fin 3) (vacuum : VacuumLabel (wallClass g false))
    (a : Fin 4) (sign : Fin 2) (either : Bool) (q : History)
    (hLive : liveExit either q = true) (reference : CarrierPair) :
    let s := chargedSeed g vacuum q
    let banked := (extract either q).1
    let ports := fun state => ReceiverCapacity.capacityPorts occupiedSlots
      (portsOf (restoringPayload g a sign) reference state)
    ReceiverCapacity.registeredTrace either s (ports s) 2 +
      ReceiverCapacity.registeredTrace either banked (ports banked) (2 * Delta - 2) = 2 := by
  unfold occupiedSlots
  simpa using
    tag_receiver_claim g vacuum a sign either q hLive reference (fun b => if b then 1 else 0)

end PMElementaryParticles.RetainedReceiverCapacity
