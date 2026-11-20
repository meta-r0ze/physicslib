import PMElementaryParticles.IsolatedExcitation
import PMElementaryParticles.WireSchedule
import PMTransport.RingReceiver
import PMTransport.Components

/-!
# Embedding the isolated excitation into the retained receiver

`IsolatedExcitation.occupiedInput` supplies one carrier label and one 16-slot
packet label.  This file records two embeddings.

* `uniformPorts` is the **uniform field (all sites, both streams)**.  It is not
  one excitation and is kept only as a control.  Its equal arrivals make the
  receiver flag zero for a reason built into the embedding, not a machine
  result.
* `localizedPorts x0 packet` is the one-excitation field: site `x0` has live
  `active packet` and record vacuum (`false`); every other site and both
  record/live values are vacuum (`false`).  This is the embedding to use for
  the localized trace.

The phase, retained requests and probe bits are not read out of the packet;
they are the open controller fields G/T and are named in `ReceiverFields`.
`wall` and `record` index the certified vacuum family from
`vacuum_nonunique`; both are carried, not selected.
-/

noncomputable section
namespace PMElementaryParticles.IsolatedExcitation

open PMConstants.PacketGaugeActions
open PMElementaryParticles.ProtocolInventory
open PMTransport
open PMTransport.RingReceiver
open PMAction

/-- Three sites is the smallest certified ring with two distinct incoming
neighbours (`RingReceiver.ring_neighbourhood`). -/
abbrev IsolatedSite := Fin 3

abbrev IsolatedRequests := LocalController.Requests
abbrev IsolatedPorts := LocalController.Ports

/-- Named open controller fields.  The phase, requests and probe are not read
out of the packet.  `wall` and `record` index the certified vacuum family from
`vacuum_nonunique`; both are carried, not selected. -/
structure ReceiverFields where
  phase : Fin Delta
  requests : IsolatedSite → IsolatedRequests
  probe : IsolatedSite → Bool
  wall : Bool
  record : Bool

/-- Number of true port bits in one two-stream port pair. -/
def portBitCountPorts (p : IsolatedPorts) : ℕ :=
  (if p.1 then 1 else 0) + (if p.2 then 1 else 0)

/-- Number of true port bits in a three-site port field. -/
def portBitCount (ports : IsolatedSite → IsolatedPorts) : ℕ :=
  ∑ x, portBitCountPorts (ports x)

/-- Uniform field: every site has the same live/record value.  This is all
sites and both streams, not one excitation. -/
def uniformPorts (packet : PacketLabel) : IsolatedSite → IsolatedPorts :=
  fun _ => (active packet, active packet)

/-- The one-excitation port field: one live packet at `x0`, record vacuum
there, and vacuum everywhere else.  Here vacuum is the Boolean value `false`;
the physical reference vector is separately indexed by `ReceiverFields`. -/
def localizedPorts (x0 : IsolatedSite) (packet : PacketLabel) :
    IsolatedSite → IsolatedPorts :=
  fun x => if x = x0 then (active packet, false) else (false, false)

/-- Uniform embedding, retained only as a control field. -/
def embed (c : Fin 3) (_vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) : State 3 :=
  (fields.phase, (fields.requests, (fields.probe, uniformPorts packet)))

/-- Localized embedding of the one-excitation field. -/
def localizedEmbed (c : Fin 3) (_vacuum : VacuumLabel c) (packet : PacketLabel)
    (x0 : IsolatedSite) (fields : ReceiverFields) : State 3 :=
  (fields.phase, (fields.requests, (fields.probe, localizedPorts x0 packet)))

theorem embed_ports_uniform (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (x : IsolatedSite) :
    (embed c vacuum packet fields).2.2.2 x = (active packet, active packet) := rfl

theorem localizedEmbed_ports (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (x0 : IsolatedSite) (fields : ReceiverFields) (x : IsolatedSite) :
    (localizedEmbed c vacuum packet x0 fields).2.2.2 x =
      (if x = x0 then (active packet, false) else (false, false)) := rfl

theorem embed_occupied_packet (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (_fields : ReceiverFields) :
    occupiedInput c vacuum packet (.inr packet) = true :=
  occupiedInput_packet c vacuum packet

/-! ## Uniform control field: equal arrivals, zero by construction -/

/-- A uniform equal port field is fixed by the guarded receiver step. -/
theorem uniform_ports_tick (either : Bool) (s : State 3) (v : Bool)
    (h : ∀ x, s.2.2.2 x = (v, v)) (x : IsolatedSite) :
    (tick 3 either s).2.2.2 x = (v, v) := by
  rw [tick_ports]
  have ha : arrivals s.2.2.2 x = (v, v) := by
    simp [arrivals, OpenReferenceFlow.streamShift, h]
  rw [ha]
  change LocalController.applyGuard
    (fun _ => exchange either (s.2.1 x)) (v, v) = (v, v)
  unfold LocalController.applyGuard
  split <;> rfl

theorem uniform_ports_iterate (either : Bool) (s : State 3) (v : Bool)
    (h : ∀ x, s.2.2.2 x = (v, v)) (k : ℕ) (x : IsolatedSite) :
    ((tick 3 either)^[k] s).2.2.2 x = (v, v) := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact uniform_ports_tick either _ v ih x

/-- On equal arrivals the receiver registers zero, under either rule. -/
theorem receiver_flag_zero_of_uniform (either : Bool) (s : State 3) (v : Bool)
    (h : ∀ x, s.2.2.2 x = (v, v)) (x : IsolatedSite) :
    receiverFlag either s x = 0 := by
  rw [receiver_flag_eq]
  have ha : arrivals s.2.2.2 x = (v, v) := by
    simp [arrivals, OpenReferenceFlow.streamShift, h]
  rw [ha]
  simp

/-- Uniform field, not one excitation: zero under AND. -/
theorem uniform_flag_zero_AND (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag false ((tick 3 false)^[k] (embed c vacuum packet fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  exact uniform_ports_iterate false _ _ (embed_ports_uniform c vacuum packet fields) k

/-- Uniform field, not one excitation: zero under OR. -/
theorem uniform_flag_zero_OR (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag true ((tick 3 true)^[k] (embed c vacuum packet fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  exact uniform_ports_iterate true _ _ (embed_ports_uniform c vacuum packet fields) k

/-- Uniform field, not one excitation: AND and OR both register zero. -/
theorem uniform_AND_OR_tie (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag false ((tick 3 false)^[k] (embed c vacuum packet fields)) x =
      receiverFlag true ((tick 3 true)^[k] (embed c vacuum packet fields)) x := by
  rw [uniform_flag_zero_AND, uniform_flag_zero_OR]

/-- Uniform control field: its 43-tick receiver sum is zero. -/
theorem uniform_period_registrations_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) :
    (∑ t : Fin Delta, ∑ x : IsolatedSite,
      receiverFlag either ((tick 3 either)^[t.val]
        (embed c vacuum packet fields)) x) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro x _
  cases either
  · exact uniform_flag_zero_AND c vacuum packet fields t.val x
  · exact uniform_flag_zero_OR c vacuum packet fields t.val x

/-! ## Occupancy checks -/

theorem portBitCount_applyGuard (g : LocalController.Guard) (p : IsolatedPorts) :
    portBitCountPorts (LocalController.applyGuard g p) = portBitCountPorts p := by
  unfold LocalController.applyGuard portBitCountPorts
  split <;> simp [add_comm]

theorem portBitCount_arrivals (ports : IsolatedSite → IsolatedPorts) :
    portBitCount (arrivals ports) = portBitCount ports := by
  unfold portBitCount portBitCountPorts arrivals OpenReferenceFlow.streamShift
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · exact Equiv.sum_comp (finRotate 3).symm
      (fun x => if (ports x).1 then 1 else 0)
  · exact Equiv.sum_comp (finRotate 3)
      (fun x => if (ports x).2 then 1 else 0)

theorem portBitCount_tick (either : Bool) (s : State 3) :
    portBitCount ((tick 3 either s).2.2.2) = portBitCount s.2.2.2 := by
  unfold portBitCount
  calc
    (∑ x, portBitCountPorts ((tick 3 either s).2.2.2 x)) =
        ∑ x, portBitCountPorts (arrivals s.2.2.2 x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [tick_ports]
      exact portBitCount_applyGuard _ _
    _ = ∑ x, portBitCountPorts (s.2.2.2 x) := portBitCount_arrivals s.2.2.2

/-- Localized occupancy: one true live bit when the packet is active, zero
otherwise. -/
theorem localizedPorts_occupancy (x0 : IsolatedSite) (packet : PacketLabel) :
    portBitCount (localizedPorts x0 packet) = if active packet then 1 else 0 := by
  rw [portBitCount, Finset.sum_eq_single_of_mem x0 (Finset.mem_univ x0)]
  · by_cases h : active packet <;>
      simp [localizedPorts, portBitCountPorts, h]
  · intro b _ hb
    simp [localizedPorts, portBitCountPorts, hb]

/-- The localized one-excitation occupancy is preserved by `tick` under both
rules, at every tick. -/
theorem localized_occupancy_preserved (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (x0 : IsolatedSite)
    (fields : ReceiverFields) (k : ℕ) :
    portBitCount (((tick 3 either)^[k]
      (localizedEmbed c vacuum packet x0 fields)).2.2.2) =
      (if active packet then 1 else 0) := by
  induction k with
  | zero => simpa [localizedEmbed] using localizedPorts_occupancy x0 packet
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [portBitCount_tick, ih]

/-- The old uniform field fails the occupancy check: six true bits when the
packet is active.  It is not one excitation. -/
theorem uniformPorts_occupancy (packet : PacketLabel) :
    portBitCount (uniformPorts packet) = if active packet then 6 else 0 := by
  by_cases h : active packet <;>
    simp [portBitCount, uniformPorts, portBitCountPorts, h]

/-! ## Separate ledger columns

The receiver registration count is measured in registrations per 43-tick
period.  The record Toll is measured in WireSchedule bit visits per label.
No certified result in this file puts those two units in one ledger, so they
are exposed as separate columns and are not added.
-/

/-- Uniform control-field receiver registrations per 43-tick period. -/
noncomputable def uniformReceiverColumn (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) : ℝ :=
  ∑ t : Fin Delta, ∑ x : IsolatedSite,
    receiverFlag either ((tick 3 either)^[t.val] (embed c vacuum packet fields)) x

theorem uniformReceiverColumn_eq_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) :
    uniformReceiverColumn either c vacuum packet fields = 0 := by
  unfold uniformReceiverColumn
  exact_mod_cast uniform_period_registrations_zero either c vacuum packet fields

/-- Record bit visits per label, a separate column with its own unit. -/
noncomputable def isolatedRecordColumn (reference : Bool) (label : Channels) : ℝ :=
  WireSchedule.bitToll reference label

/-! ## The packet lifts

The certified lifts in `PMTransport.Components` move the packet bank.  They do
not select receiver booking ticks.  `hold_cell_fixed` and `fifo_lift_differs`
identify the two lift actions; no tick set is derived from them.
-/

/-- Hold keeps the packet in cell zero. -/
theorem hold_cell_fixed (R : ℕ) (packet : PacketLabel) :
    (Equiv.refl (Components.PacketBank R)) (Pi.single ((0 : Fin (R + 1)), packet) 1) =
      Pi.single ((0 : Fin (R + 1)), packet) 1 := rfl

/-- The FIFO lift differs from the identity lift on the certified packet bank. -/
theorem fifo_lift_differs :
    Components.fifoEquiv 1 ≠ Equiv.refl (Components.PacketBank 1) := by
  obtain ⟨bank, h⟩ := Components.joint_two_fifo_placements_differ
    (I := Unit) (core := id) () ((Sum.inr (Sum.inr (Sum.inl 1))) : PacketLabel)
  intro he
  apply h
  simp [Components.jointTick, he]

end PMElementaryParticles.IsolatedExcitation
