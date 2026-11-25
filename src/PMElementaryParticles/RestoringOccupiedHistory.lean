import PMElementaryParticles.IsolatedReceiverTrace
import PMKAutomaton.RestoringRingHistory

/-!
# The closed restoring history in the occupied EP receiver encoding

The existing isolated embedding sends an active packet to the sole true live
bit. The same occupied preparation therefore realizes the restoring ring
seed with the stated controller fields. This attachment concerns the
receiver encoding and occupancy. The joint selection of controller fields
and the coherent carrier readout are separate inputs.
-/

namespace PMElementaryParticles.IsolatedExcitation

open PMAction ProtocolInventory PMKAutomaton
open RestoringRingHistory

/-- Use the retained controller and probe fields of the closed restoring
seed in the existing localized occupied embedding. -/
def restoringFields (q : History) (wall record : Bool) : ReceiverFieldsN Delta :=
  ⟨0, (seed q).2.1, (seed q).2.2.1, wall, record⟩

theorem localized_restoring_seed (c : Fin 3) (vacuum : VacuumLabel c)
    (packet : PacketLabel) (hpacket : active packet = true) (q : History)
    (wall record : Bool) :
    localizedEmbedN Delta c vacuum packet 42 (restoringFields q wall record) = seed q := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  funext x
  change localizedPortsN Delta 42 packet x = (decide (x = (42 : Fin Delta)), false)
  by_cases hx : x = (42 : Fin Delta) <;> simp [localizedPortsN, hx, hpacket]

/-- The restoring ring's seed is the encoded occupied EP input. Its
one-packet occupancy is preserved at every tick. The live exit after two
visits and full return after two periods follow from the lower-layer trace. -/
theorem occupied_restoring_history (c : Fin 3) (vacuum : VacuumLabel c)
    (packet : PacketLabel) (hpacket : active packet = true) (q : History)
    (wall record either : Bool) :
    let s := localizedEmbedN Delta c vacuum packet 42 (restoringFields q wall record)
    Admitted (occupiedInput c vacuum packet) ∧
      (∀ n, portBitCountN Delta (((RingReceiver.tick Delta either)^[n] s).2.2.2) = 1) ∧
      (RingReceiver.tick Delta either)^[2 * Delta] s = s ∧
      RingReceiver.slotValue (((RingReceiver.tick Delta either)^[2] s).2.2.2) (42, false) =
        (RingReceiver.exchange either q.1 && RingReceiver.exchange either q.2) := by
  intro s
  have hs : s = seed q := localized_restoring_seed c vacuum packet hpacket q wall record
  refine ⟨occupiedInput_admitted c vacuum packet, ?_, ?_, ?_⟩
  · intro n
    simpa only [s, hpacket, ite_true] using localized_occupancy_preservedN Delta either c vacuum
      packet 42 (restoringFields q wall record) n
  · rw [hs]
    exact seed_returns either q
  · rw [hs]
    exact live_exit either q

end PMElementaryParticles.IsolatedExcitation
