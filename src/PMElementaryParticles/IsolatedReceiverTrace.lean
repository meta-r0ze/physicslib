import PMElementaryParticles.IsolatedExcitation
import PMTransport.RingReceiver
import PMTransport.Components

/-!
# Embedding the isolated excitation into the retained receiver

`IsolatedExcitation.occupiedInput` supplies one carrier label and one 16-slot
packet label.  This file embeds that occupancy into a three-site retained
receiver state.  The packet label supplies the common port value read by both
streams: with one excitation there is no second arrival.  The phase, retained
requests and probe bits are **not** derived from the packet; they are the open
controller fields G/T, so they are named in `ReceiverFields` and kept explicit.
The two rest modes from `vacuum_nonunique` are indexed by the `wall`/`record`
arguments of `OccupiedInput` but do not further constrain the Boolean receiver.

The trace below is the literal iteration of `RingReceiver.tick`.  On the
uniform two-stream port field both arrivals are equal at every site and tick,
so `RingReceiver.receiver_flag_eq` gives zero registration under AND and under
OR.  This is the trace result for the isolated excitation; it is independent
of the named controller fields.
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

/-- Named open controller fields.  These are not read out of the packet. -/
structure ReceiverFields where
  phase : Fin Delta
  requests : IsolatedSite → IsolatedRequests
  probe : IsolatedSite → Bool

/-- Both streams read the same occupied packet label.  This is the one-
excitation port field; it is derived from `packet` and the certified inventory
predicate `active`, not from a supplied rate or slot set. -/
def isolatedPorts (packet : PacketLabel) : IsolatedSite → IsolatedPorts :=
  fun _ => (active packet, active packet)

/-- The Task 2 embedding of an occupied input into `RingReceiver.State 3`.
The occupied input is carried in the vocabulary even though only its packet
label fixes a derived field; the other fields are the named `ReceiverFields`. -/
def embed (c : Fin 3) (_vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) : State 3 :=
  (fields.phase, (fields.requests, (fields.probe, isolatedPorts packet)))

theorem embed_ports_uniform (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (x : IsolatedSite) :
    (embed c vacuum packet fields).2.2.2 x = (active packet, active packet) := rfl

theorem embed_occupied_packet (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (_fields : ReceiverFields) :
    occupiedInput c vacuum packet (.inr packet) = true :=
  occupiedInput_packet c vacuum packet

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

/-- Task 3(a): at every site and tick of the literal 43-tick iteration, the
embedded isolated excitation registers zero under AND. -/
theorem isolated_flag_zero_AND (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag false ((tick 3 false)^[k] (embed c vacuum packet fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  exact uniform_ports_iterate false _ _ (embed_ports_uniform c vacuum packet fields) k

/-- Task 3(a): the same zero under OR. -/
theorem isolated_flag_zero_OR (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag true ((tick 3 true)^[k] (embed c vacuum packet fields)) x = 0 := by
  apply receiver_flag_zero_of_uniform
  exact uniform_ports_iterate true _ _ (embed_ports_uniform c vacuum packet fields) k

/-- AND and OR tie at every isolated site and tick because both register zero. -/
theorem isolated_AND_OR_tie (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (k : ℕ) (x : IsolatedSite) :
    receiverFlag false ((tick 3 false)^[k] (embed c vacuum packet fields)) x =
      receiverFlag true ((tick 3 true)^[k] (embed c vacuum packet fields)) x := by
  rw [isolated_flag_zero_AND, isolated_flag_zero_OR]

/-- The booked receiver registration sum over a full 43-tick isolated period
is zero, for either rule.  This is the literal sum of `receiverFlag` on the
iterated embedded state. -/
theorem isolated_period_registrations_zero (either : Bool) (c : Fin 3)
    (vacuum : VacuumLabel c) (packet : PacketLabel) (fields : ReceiverFields) :
    (∑ t : Fin Delta, ∑ x : IsolatedSite,
      receiverFlag either ((tick 3 either)^[t.val]
        (embed c vacuum packet fields)) x) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro x _
  cases either
  · exact isolated_flag_zero_AND c vacuum packet fields t.val x
  · exact isolated_flag_zero_OR c vacuum packet fields t.val x

/-! ## Task 4: the packet lifts

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
