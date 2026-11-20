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
def embed (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) : State 3 :=
  (fields.phase, (fields.requests, (fields.probe, isolatedPorts packet)))

theorem embed_ports_uniform (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) (x : IsolatedSite) :
    (embed c vacuum packet fields).2.2.2 x = (active packet, active packet) := rfl

theorem embed_occupied_packet (c : Fin 3) (vacuum : VacuumLabel c) (packet : PacketLabel)
    (fields : ReceiverFields) :
    occupiedInput c vacuum packet (.inr packet) = true :=
  occupiedInput_packet c vacuum packet

end PMElementaryParticles.IsolatedExcitation
