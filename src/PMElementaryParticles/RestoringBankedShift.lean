import PMElementaryParticles.RestoringWallShift
import PMKAutomaton.RestoringExtraction

/-!
# The class word on the extracted restoring payload

The bank is initialized with the vector-class reference. Two receiver
visits route the gapped carrier pair to the live exit. The reversible
exchange carries that pair into the bank and leaves a uniform reference
field. Running the existing class word on the bank produces the target
address and signed carrier. The bank exchange is a booked operation;
its pulse duration and physical implementation are separate inputs.
-/

namespace PMElementaryParticles.RestoringWallShift

open PMAction PMKAutomaton
open GluedRegister ControlledGluedRegister ProtocolInventory GappedGluedCrossing
open PMConstants.PacketGaugeActions
open RestoringExtraction RestoringRingHistory

/-- After the booked two-visit extraction, the class word acts on the
retained typed payload and leaves the receiver's reference field intact. -/
theorem banked_exit_then_class_shift (g : Fin 3) (c : Channels) (i : Fin 4) (s : Fin 2)
    (hc : active c = false) (either : Bool) (q : History) (hLive : liveExit either q = true)
    (referenceAmplitude referenceLabel : Fin 8) :
    let reference := (frame 0 referenceAmplitude, frame 0 referenceLabel)
    let payload := runGappedCrossing g (encode g c (signedAxis i s))
    let prepared := liftPorts reference payload (seed q).2.2.2
    let extracted := exchangeLive (42 : Fin Delta)
      ((valueStep either (seed q).2.1)^[2] prepared, reference)
    extracted.1 = (fun _ => (reference, reference)) ∧
      runClassShift extracted.2 = encode g (opposite c) (signedAxis (i + 2) s) := by
  intro reference payload prepared extracted
  have he : extracted = (fun _ => (reference, reference), payload) :=
    extract_values either q hLive reference payload
  rw [he]
  exact ⟨rfl, cross_then_class_shift g c i s hc⟩

end PMElementaryParticles.RestoringWallShift
