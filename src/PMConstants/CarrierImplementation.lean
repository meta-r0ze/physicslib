import PMConstants.CarrierActions
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A finite register realization of the carrier actions. This is a local
internal-state model, not a completed E8 vacuum schedule or a cost-selection law. -/
noncomputable section
namespace PMConstants.CarrierImplementation
open PMConstants.CarrierActions
open Finset

abbrev Payload := Packet → Bool
abbrev State := Fin PMSubstrate.E8Values.Delta × Payload

def onPayload (e : Equiv.Perm Packet) : Equiv.Perm Payload where
  toFun p := p ∘ e.symm
  invFun p := p ∘ e
  left_inv p := by funext v; simp
  right_inv p := by funext v; simp

/-- The global clock still advances; the carrier gate acts on internal payload. -/
def step (e : Equiv.Perm Packet) : Equiv.Perm State :=
  Equiv.prodCongr (finRotate PMSubstrate.E8Values.Delta) (onPayload e)

theorem finite_state_count : Fintype.card State=43*2^16 := by
  simp [State, Payload, Packet, Fintype.card_prod,
    Fintype.card_sum, PMAction.CarrierEvents.carrier_card]

theorem identity_preserved (e : Equiv.Perm Packet) : Function.Injective (step e) :=
  (step e).injective

def population (p : Payload) : ℕ := ∑ v, (p v).toNat

theorem population_preserved (e : Equiv.Perm Packet) (s : State) :
    population (step e s).2=population s.2 :=
  Equiv.sum_comp e.symm (fun v => (s.2 v).toNat)

theorem clock_advance (e : Equiv.Perm Packet) (s : State) : (step e s).1=finRotate PMSubstrate.E8Values.Delta s.1 := rfl

theorem payload_clock_independent (e : Equiv.Perm Packet) (c d : Fin PMSubstrate.E8Values.Delta) (p : Payload) :
    (step e (c,p)).2=(step e (d,p)).2 := rfl

/-- An operational field is affected exactly when the actual carrier label moves. -/
theorem field_changed_iff (e : Equiv.Perm Packet) (v : Packet) :
    (∃ p : Payload, onPayload e p v ≠ p v) ↔ e v ≠ v := by
  constructor
  · rintro ⟨p,hp⟩ he
    have hi : e.symm v=v := by simpa using congrArg e.symm he.symm
    exact hp (by simp [onPayload, hi])
  · intro he
    have hi : e.symm v ≠ v := by
      intro hh
      apply he
      simpa using (congrArg e hh).symm
    refine ⟨fun w => decide (w=v), ?_⟩
    simp [onPayload, hi]

/-- Exact affected payload sets, independent of the resource-naming convention. -/
theorem weak_fields (v : Packet) :
    (∃ p : Payload, onPayload weak p v ≠ p v) ↔ v ∈ weakSupport := by
  rw [field_changed_iff]
  simp [weakSupport]

theorem colour_fields (v : Packet) :
    (∃ a b : Fin 3, ∃ p : Payload, onPayload (colour a b) p v ≠ p v) ↔ v ∈ colourSupport := by
  simpa only [field_changed_iff] using colour_exists_iff v

/-- The two action families can share exactly the same clock advancement.
This is not a theorem that clock maintenance costs zero. -/
theorem shared_clock (e f : Equiv.Perm Packet) (s : State) :
    (step e s).1=(step f s).1 := rfl

end PMConstants.CarrierImplementation
