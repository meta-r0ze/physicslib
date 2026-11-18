import PMElementaryParticles.ControlledGluedRegister
import PMElementaryParticles.RefreshMap

/-!
# Constraints on a Toll from the glued protocol label

The active channels determine the four comparison protocols. Colour relabeling
has precisely those four orbits. A reversible colour-equivariant label update
preserves the colourless sector. A fixed schedule of weak and colour relabelings,
priced by changed labels, gives both weak partners the same Toll even if the
primitive prices differ.

The root-displacement test uses every forward displacement in the reference
vector frame, so it tests the proposed event-count ladder before imposing
gauge equivariance. The algebraic tests take a strict comparison order as a
hypothesis and use no fitted masses or weights.
-/

noncomputable section
namespace PMElementaryParticles.ProtocolToll

open PMConstants.PacketGaugeActions ProtocolInventory
open ControlledGluedRegister GluedRegister

theorem same_active_colour_orbit : ∀ c d : Channels, active c = true → active d = true →
    (baseProtocol c = baseProtocol d ↔ ∃ a b : Fin 3, permuteColour a b c = d) := by
  decide +kernel

theorem colour_fixed_iff : ∀ c : Channels,
    (∀ a b : Fin 3, permuteColour a b c = c) ↔ colourBulk c = false := by
  decide +kernel

/-- A reversible colour-equivariant update on the label alone keeps the
colourless and coloured channels separate. -/
theorem equivariant_preserves_colourBulk (f : Channels → Channels)
    (hf : Function.Injective f)
    (hc : ∀ a b c, permuteColour a b (f c) = f (permuteColour a b c)) (c : Channels) :
    colourBulk (f c) = colourBulk c := by
  have h : ((∀ a b, permuteColour a b (f c) = f c) ↔ ∀ a b, permuteColour a b c = c) := by
    constructor
    · intro h a b
      exact hf ((hc a b c).symm.trans (h a b))
    · intro h a b
      rw [hc, h a b]
  rw [colour_fixed_iff, colour_fixed_iff] at h
  cases h₁ : colourBulk (f c) <;> cases h₂ : colourBulk c <;> simp_all

/-- The relabelings already defined on the protocol packet. -/
inductive Gate where
  | weak
  | colour (a b : Fin 3)

def Gate.step : Gate → Channels → Channels
  | .weak => flipWeak
  | .colour a b => permuteColour a b

private theorem step_weak (gate : Gate) (c : Channels) :
    gate.step (flipWeak c) = flipWeak (gate.step c) := by
  cases gate with
  | weak => rfl
  | colour a b =>
    change permuteColour a b (flipWeak c) = flipWeak (permuteColour a b c)
    revert a b c
    decide +kernel

/-- Charge a primitive when it changes the incoming label. -/
def eventToll (price : Gate → ℝ) : List Gate → Channels → ℝ
  | [], _ => 0
  | gate :: rest, c =>
    (if gate.step c = c then 0 else price gate) + eventToll price rest (gate.step c)

theorem eventToll_weak_partners (price : Gate → ℝ) (word : List Gate) (c : Channels) :
    eventToll price word (flipWeak c) = eventToll price word c := by
  induction word generalizing c with
  | nil => rfl
  | cons gate rest ih =>
    have hinj : Function.Injective flipWeak :=
      (show Function.Involutive flipWeak from RefreshMap.two_ticks).injective
    simp [eventToll, step_weak, hinj.eq_iff, ih]

/-- A candidate displacement in the reference frame, with nonnegative clock component. -/
def ForwardShift (c d : Channels) : Prop :=
  ∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧ 0 ≤ root i j s t 0 ∧
    carrier 0 (labelIndex d) = carrier 0 (labelIndex c) + root i j s t

instance (c d : Channels) : Decidable (ForwardShift c d) := by
  unfold ForwardShift
  infer_instance

private def neutrino : Channels := .inr (.inr (.inl 0))
private def electron : Channels := flipWeak neutrino
private def up : Channels := .inl (0, 0)
private def down : Channels := flipWeak up

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The unrestricted forward displacement graph bypasses the proposed ladder
in both directions. -/
theorem forward_shortcuts :
    (∀ c : Channels, active c = true →
      (baseProtocol c = some .electron ∨ baseProtocol c = some .down) →
      ∃ d : Channels, active d = true ∧ baseProtocol d = some .up ∧ ForwardShift c d) ∧
    (∀ c : Channels, active c = true → baseProtocol c = some .up → ForwardShift c neutrino) := by
  decide +kernel

/-- An odd scalar reading followed by a monotone map cannot produce the
comparison order on the active packet. -/
theorem no_monotone_odd_toll (f read : Channels → ℝ) (map : ℝ → ℝ)
    (hread : ∀ c, read c = map (f c)) (hmono : Monotone map)
    (hodd : ∀ c, active c = true → f (flipWeak c) = -f c) :
    ¬ (read neutrino < read electron ∧ read electron < read down ∧ read down < read up) := by
  rintro ⟨hne, hed, hdu⟩
  have reflect {a b : Channels} (h : read a < read b) : f a < f b := by
    apply lt_of_not_ge
    intro hab
    apply (not_le_of_gt h)
    simpa only [hread] using hmono hab
  have hel : f electron = -f neutrino := hodd neutrino rfl
  have hdn : f down = -f up := hodd up rfl
  linarith [reflect hne, reflect hed, reflect hdu]

/-- A positive sector factor times a sign factor gives the same ordering of
signs in both sectors. -/
theorem no_separable_toll (lepton coloured positive negative : ℝ)
    (hl : 0 < lepton) (hc : 0 < coloured) :
    ¬ (lepton * positive < lepton * negative ∧ coloured * negative < coloured * positive) := by
  rintro ⟨hl', hc'⟩
  exact (lt_of_mul_lt_mul_left hl' hl.le).not_gt (lt_of_mul_lt_mul_left hc' hc.le)

end PMElementaryParticles.ProtocolToll
