import PMElementaryParticles.ControlledGluedRegister
import PMTransport.Machine.ReferenceClassHop
import PMTransport.Machine.RegisterControl

/-!
# Finite control of the direct heavy flip

The endpoints use the glued crossing word in the forward direction and its inverse on return.
The generation tag addresses the reference-wall direct insertion. The two bits record the
colour orbit of the signed label, independently of the amplitude carrier and wall. A supplied
record bank and a supplied pulse give a reversible register realization. Neither the bank's
preparation nor the native firing law is selected by this construction.
-/

noncomputable section
namespace PMElementaryParticles.HeavyFlipControl

open ControlledGluedRegister PMConstants.PacketGaugeActions
open PMAction

abbrev Wire := Fin 3 × Channels × Fin 8
abbrev Record := Bool × Bool

local instance : DecidableEq Wire := Classical.decEq _
local instance : Fintype Wire := inferInstanceAs (Fintype (Fin 3 × Channels × Fin 8))

/-- The four colour orbits are distinguished by their axis sector and sign. -/
def labelRecord (c : Channels) : Record :=
  (decide ((labelIndex c).val < 2), decide ((labelIndex c).val % 2 = 1))

theorem record_opposite (c : Channels) : labelRecord (opposite c) = labelRecord c := by
  simp only [labelRecord, opposite_label]

theorem record_colour : ∀ (a b : Fin 3) (c : Channels),
    labelRecord (permuteColour a b c) = labelRecord c := by
  decide +kernel

/-- On the static wall the record separates the four signed species and ignores quark colour. -/
theorem static_record_codes : ∀ a : Fin 3,
    labelRecord (.inr (.inr (.inr 1))) = (true, true) ∧
      labelRecord (.inr (.inl (a, 1))) = (false, true) ∧
      labelRecord (.inr (.inl (a, 0))) = (false, false) ∧
      labelRecord (.inr (.inr (.inr 0))) = (true, false) := by
  decide +kernel

/-- The reference-wall direct path is the one avoiding class zero at both endpoints. -/
def direct (g : Fin 3) : Prop := g + 1 ≠ 0 ∧ g - 1 ≠ 0

instance (g : Fin 3) : Decidable (direct g) :=
  inferInstanceAs (Decidable (g + 1 ≠ 0 ∧ g - 1 ≠ 0))

theorem direct_iff (g : Fin 3) : direct g ↔ g = 0 := by
  rw [direct, ← not_or, ReferenceClassHop.touches_reference_class, not_ne_iff]

/-- The untagged glued root alone cannot address this event. -/
theorem no_root_only_direct_address (read : GluedRegister.Wt × GluedRegister.Wt → Bool)
    (correct : ∀ g c a, read (encode g c a) = true ↔ direct g) : False := by
  let c : Channels := .inl (0, 0)
  let d : Channels := .inr (.inl (0, 0))
  have h : encode 0 c 2 = encode 1 d 2 := by decide +kernel
  have hc := (correct 0 c 2).mpr ((direct_iff 0).mpr rfl)
  rw [h] at hc
  exact (by decide : (1 : Fin 3) ≠ 0) ((direct_iff 1).mp ((correct 1 d 2).mp hc))

/-- Write the incoming label's orbit into a clean record on the direct path.
Each bit is written by a conditional exchange with its other value. -/
def writeRecord : Equiv.Perm (Wire × Record) :=
  Equiv.prodCongrRight fun w =>
    if direct w.1 then
      Equiv.prodCongr (Equiv.swap false (labelRecord w.2.1).1)
        (Equiv.swap false (labelRecord w.2.1).2)
    else Equiv.refl _

@[simp] theorem write_clean (g : Fin 3) (c : Channels) (a : Fin 8) :
    writeRecord ((g, c, a), (false, false)) =
      ((g, c, a), if direct g then labelRecord c else (false, false)) := by
  by_cases h : direct g <;> simp [writeRecord, h]

/-- Apply the glued endpoint exchange only in the selected record block on the
reference-wall direct path. Both the generation address and the record survive. -/
def controlledFlip (r : Record) : Equiv.Perm (Wire × Record) where
  toFun p := if direct p.1.1 ∧ p.2 = r then ((p.1.1, opposite p.1.2.1, p.1.2.2), p.2) else p
  invFun p := if direct p.1.1 ∧ p.2 = r then ((p.1.1, opposite p.1.2.1, p.1.2.2), p.2) else p
  left_inv := by
    rintro ⟨⟨g, c, a⟩, s⟩
    by_cases h : direct g ∧ s = r <;> simp [h, opposite_twice]
  right_inv := by
    rintro ⟨⟨g, c, a⟩, s⟩
    by_cases h : direct g ∧ s = r <;> simp [h, opposite_twice]

theorem flip_involutive (r : Record) : Function.Involutive (controlledFlip r) :=
  (controlledFlip r).left_inv

theorem flip_light (r s : Record) (g : Fin 3) (hg : g ≠ 0) (c : Channels) (a : Fin 8) :
    controlledFlip r ((g, c, a), s) = ((g, c, a), s) := by
  simp [controlledFlip, direct_iff, hg]

theorem flip_encoded (c : Channels) (a : Fin 8) (r : Record) (hc : ProtocolInventory.active c = false) :
    let w := (controlledFlip r ((0, c, a), r)).1
    encode w.1 w.2.1 w.2.2 = GluedRegister.runCrossing (encode 0 c a) := by
  simp [controlledFlip, direct_iff, runCrossing_encode 0 c a hc]

/-- The word on the two occupied banks implements the recorded endpoint permutation. -/
theorem registered_word (r : Record) (p : Wire × Record) :
    RegisterControl.extend (controlledFlip r)
        (RegisterControl.extend writeRecord (IndependentRegisters.encode p)) =
      IndependentRegisters.encode (controlledFlip r (writeRecord p)) := by
  rw [RegisterControl.extend_encode, RegisterControl.extend_encode]

/-- Each record block admits a unitary spectral phase of its controlled flip
in the mathematical register model. Composing these gives independent phase controls. -/
theorem registered_phase_unitary (r : Record) (z : ℂ) (hz : star z * z = 1) :
    InvolutionComparison.phase ((RegisterControl.extend (controlledFlip r)).permMatrix ℂ) z
      ∈ unitary (Matrix (IndependentRegisters.Configuration Wire Record)
        (IndependentRegisters.Configuration Wire Record) ℂ) :=
  RegisterControl.phase_unitary _ (flip_involutive r) z hz

end PMElementaryParticles.HeavyFlipControl
