import PMElementaryParticles.GluedRegister
import PMElementaryParticles.ProtocolInventory
import PMConstants.ChannelOccupancy
import PMConstants.SectorLinks

/-!
# The glued register with wall-controlled weak refresh

Use the active wall for the eight left-handed channels and the static wall for
the eight right-handed channels, as in the zero-kernel wall convention. The
positive lepton carrier reads as the neutrino on the active wall and as the
vacancy on the static wall. Triality transports the vector frame for both
the amplitude and the protocol label.

This realizes the finite weak and colour relabelings and gives a wall-local
root reflection at fixed generation. Reversing the bank and preserving the
transported signed label selects a unique partner and preserves electric
charge. The static neutral slot is the active neutrino's crossing partner,
even though the light inventory calls that slot a vacancy. The crossing
pairs channels; occupying the static slot in the light spectrum requires a
dynamical rule.
-/

namespace PMElementaryParticles.ControlledGluedRegister

open GluedRegister ProtocolInventory PMConstants.PacketGaugeActions

/-- The signed axis in the vector frame, with axis zero reserved for leptons. -/
def labelIndex : Channels → Fin 8
  | .inl (c, s) | .inr (.inl (c, s)) => ⟨2 * (c.val + 1) + s.val, by omega⟩
  | .inr (.inr (.inl s)) | .inr (.inr (.inr s)) => ⟨s.val, by omega⟩

/-- Activity and the carrier index together identify the inventory channel. -/
def channelCode (c : Channels) : Bool × Fin 8 := (active c, labelIndex c)

theorem channelCode_bijective : Function.Bijective channelCode := by decide +kernel

/-- A wall exchange in the same signed-axis frame. -/
def opposite : Channels → Channels
  | .inl q => .inr (.inl q)
  | .inr (.inl q) => .inl q
  | .inr (.inr (.inl s)) => .inr (.inr (.inr s))
  | .inr (.inr (.inr s)) => .inr (.inr (.inl s))

theorem opposite_twice : ∀ c, opposite (opposite c) = c := by decide +kernel

theorem opposite_active : ∀ c, active (opposite c) = !active c := by decide +kernel

theorem opposite_label : ∀ c, labelIndex (opposite c) = labelIndex c := by decide +kernel

theorem opposite_colour : ∀ (a b : Fin 3) (c : Channels),
    opposite (permuteColour a b c) = permuteColour a b (opposite c) := by
  decide +kernel

theorem opposite_charge (c : Channels) : ChargeProtocols.Q (opposite c) = ChargeProtocols.Q c := by
  rw [ChargeProtocols.Q_eval, ChargeProtocols.Q_eval]
  rcases c with q | q | s | s <;> rfl

/-- The signed label determines a unique opposite-bank partner. -/
theorem eq_opposite_iff (c d : Channels) :
    d = opposite c ↔ active d = !active c ∧ labelIndex d = labelIndex c := by
  constructor
  · rintro rfl
    exact ⟨opposite_active c, opposite_label c⟩
  · rintro ⟨hw, hl⟩
    exact channelCode_bijective.1 (Prod.ext (hw.trans (opposite_active c).symm)
      (hl.trans (opposite_label c).symm))

/-- The crossing convention preserves electric charge. Each static-to-active
pair differs by one unit of hypercharge (three units in the packet tag). -/
theorem opposite_hypercharge_step : ∀ c : Channels, active c = false →
    (PMConstants.ChannelOccupancy.tag c).2.2 -
      (PMConstants.ChannelOccupancy.tag (opposite c)).2.2 =
        if (labelIndex c).val % 2 = 0 then (3 : ℤ) else -3 := by
  decide +kernel

/-- The glued endpoint charge difference matches the existing Paper III
scalar link or its conjugate, including the neutral pair. -/
theorem opposite_scalar_link (c : Channels) (hc : active c = false)
    (h : ℚ) (hlink : PMConstants.SectorLinks.OneLink PMConstants.Hypercharge.standard h) :
    ((PMConstants.ChannelOccupancy.tag c).2.2 : ℚ) / 3 -
      ((PMConstants.ChannelOccupancy.tag (opposite c)).2.2 : ℚ) / 3 =
        if (labelIndex c).val % 2 = 0 then h else -h := by
  have hh : h = 1 := by
    have hstd := PMConstants.SectorLinks.standard_links
    unfold PMConstants.SectorLinks.OneLink at hlink
    exact (congrArg Prod.fst (hstd.symm.trans hlink)).symm
  subst h
  have hd := opposite_hypercharge_step c hc
  by_cases he : (labelIndex c).val % 2 = 0
  · rw [ite_eq_left he] at hd ⊢
    have hr : ((PMConstants.ChannelOccupancy.tag c).2.2 : ℚ) -
        ((PMConstants.ChannelOccupancy.tag (opposite c)).2.2 : ℚ) = 3 := by
      exact_mod_cast hd
    linarith
  · rw [ite_eq_right he] at hd ⊢
    have hr : ((PMConstants.ChannelOccupancy.tag c).2.2 : ℚ) -
        ((PMConstants.ChannelOccupancy.tag (opposite c)).2.2 : ℚ) = -3 := by
      exact_mod_cast hd
    linarith

/-- Transport from the reference vector class through the triality cycle. -/
def transport : Fin 3 → Wt → Wt
  | 0, w => w
  | 1, w => triality w
  | 2, w => triality (triality w)

def frame (x : Fin 3) (a : Fin 8) : Wt := transport x (carrier 0 a)

theorem frame_succ : ∀ (x : Fin 3) (a : Fin 8), triality (frame x a) = frame (x + 1) a := by
  decide +kernel

theorem frame_carrier : ∀ (x : Fin 3) (a : Fin 8), ∃ b : Fin 8, frame x a = carrier x b := by
  decide +kernel

theorem frame_onto : ∀ (x : Fin 3) (b : Fin 8), ∃ a : Fin 8, frame x a = carrier x b := by
  decide +kernel

theorem frame_injective : ∀ (x : Fin 3) (a b : Fin 8), frame x a = frame x b → a = b := by
  decide +kernel

theorem frame_class_unique : ∀ (x y : Fin 3) (a b : Fin 8),
    frame x a = frame y b → x = y := by decide +kernel

/-- Wall F is active, wall T is static. -/
def wallClass (g : Fin 3) (b : Bool) : Fin 3 := if b then g - 1 else g + 1

theorem wallClass_injective : ∀ g : Fin 3, Function.Injective (wallClass g) := by
  decide +kernel

def place (b : Bool) (amp label : Wt) : Wt × Wt :=
  if b then (label, amp) else (amp, label)

def encode (g : Fin 3) (c : Channels) (amp : Fin 8) : Wt × Wt :=
  let x := wallClass g (active c)
  place (active c) (frame x amp) (frame x (labelIndex c))

private theorem first_frame (g : Fin 3) (c : Channels) (a : Fin 8) :
    ∃ i : Fin 8, (encode g c a).1 = frame (wallClass g (active c)) i := by
  cases hc : active c
  · exact ⟨a, by simp [encode, place, hc]⟩
  · exact ⟨labelIndex c, by simp [encode, place, hc]⟩

theorem encode_glued (g : Fin 3) (c : Channels) (amp : Fin 8) :
    ∃ a b : Fin 8, encode g c amp =
      (carrier (wallClass g (active c)) a, carrier (wallClass g (active c)) b) := by
  obtain ⟨i, hi⟩ := frame_carrier (wallClass g (active c)) amp
  obtain ⟨j, hj⟩ := frame_carrier (wallClass g (active c)) (labelIndex c)
  dsimp only [encode]
  rw [hi, hj]
  cases active c
  · exact ⟨i, j, rfl⟩
  · exact ⟨j, i, rfl⟩

theorem encode_injective (g : Fin 3) :
    Function.Injective (fun p : Channels × Fin 8 => encode g p.1 p.2) := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  change encode g c a = encode g d b at h
  obtain ⟨i, hi⟩ := first_frame g c a
  obtain ⟨j, hj⟩ := first_frame g d b
  have hc : active c = active d := wallClass_injective g
    (frame_class_unique _ _ i j (hi.symm.trans ((congrArg Prod.fst h).trans hj)))
  have hframes :
      frame (wallClass g (active c)) a = frame (wallClass g (active c)) b ∧
      frame (wallClass g (active c)) (labelIndex c) =
        frame (wallClass g (active c)) (labelIndex d) := by
    unfold encode at h
    rw [← hc] at h
    cases hs : active c <;> simpa [place, hs, eq_comm, and_comm] using h
  exact Prod.ext
    (channelCode_bijective.injective (Prod.ext hc (frame_injective _ _ _ hframes.2)))
    (frame_injective _ _ _ hframes.1)

theorem weak_label : ∀ (x : Fin 3) (c : Channels),
    frame x (labelIndex (flipWeak c)) =
      if active c then -frame x (labelIndex c) else frame x (labelIndex c) := by
  decide +kernel

theorem weak_active : ∀ c, active (flipWeak c) = active c := by decide +kernel

/-- A weak operation applies the antipode to the label on the active wall. -/
theorem encode_weak (g : Fin 3) (c : Channels) (amp : Fin 8) :
    encode g (flipWeak c) amp =
      let x := wallClass g (active c)
      place (active c) (frame x amp)
        (if active c then -frame x (labelIndex c) else frame x (labelIndex c)) := by
  simp only [encode, weak_active, weak_label]

/-- Colour permutations in each class use the conjugate of the vector-frame action. -/
def colour (x : Fin 3) (a b : Fin 3) (w : Wt) : Wt :=
  transport x (transport (-x) w ∘ Equiv.swap
    (PMConstants.CarrierActions.colourAxis a) (PMConstants.CarrierActions.colourAxis b))

theorem colour_label : ∀ (x : Fin 3) (a b : Fin 3) (c : Channels),
    frame x (labelIndex (permuteColour a b c)) = colour x a b (frame x (labelIndex c)) := by
  decide +kernel

theorem colour_active : ∀ (a b : Fin 3) (c : Channels),
    active (permuteColour a b c) = active c := by decide +kernel

theorem encode_colour (g : Fin 3) (a b : Fin 3) (c : Channels) (amp : Fin 8) :
    encode g (permuteColour a b c) amp =
      let x := wallClass g (active c)
      place (active c) (frame x amp) (colour x a b (frame x (labelIndex c))) := by
  simp only [encode, colour_active, colour_label]

/-- A pure root in the chosen amplitude factor preserves the channel. -/
theorem wall_reflection (g : Fin 3) (c : Channels) (amp : Fin 8) (i j : Fin 4)
    (s t : Bool) (hij : i ≠ j) :
    ∃ amp' : Fin 8, reflectPair (place (active c) (root i j s t) 0) (encode g c amp) =
      encode g c amp' := by
  let x := wallClass g (active c)
  obtain ⟨k, hk⟩ := frame_carrier x amp
  obtain ⟨l, hl⟩ := wallStep_class x k i j s t hij
  obtain ⟨amp', ha⟩ := frame_onto x l
  have hr : refl (root i j s t) (frame x amp) = frame x amp' := by
    rw [hk, hl, ha]
  refine ⟨amp', ?_⟩
  unfold encode
  change reflectPair (place (active c) _ 0) (place (active c) (frame x amp) _) =
    place (active c) (frame x amp') _
  rw [← hr]
  cases active c <;>
    simp [place, reflectPair, dot] <;> rfl

/-- Read the wall from its glue class in a specified generation. -/
def onWall (g : Fin 3) (b : Bool) (w : Wt × Wt) : Bool :=
  decide (∃ a : Fin 8, w.1 = frame (wallClass g b) a)

theorem onWall_encode (g : Fin 3) (c : Channels) (amp : Fin 8) (b : Bool) :
    onWall g b (encode g c amp) = true ↔ active c = b := by
  obtain ⟨a, ha⟩ := first_frame g c amp
  simp only [onWall, decide_eq_true_eq, ha]
  constructor
  · rintro ⟨i, hi⟩
    exact wallClass_injective g (frame_class_unique _ _ _ _ hi)
  · rintro rfl
    exact ⟨a, rfl⟩

/-- Reflect in the amplitude factor on one wall, with a glue-class control. -/
def controlledReflection (g : Fin 3) (b : Bool) (r : Wt) (w : Wt × Wt) : Wt × Wt :=
  if onWall g b w then reflectPair (place b r 0) w else w

theorem controlledReflection_on_wall (g : Fin 3) (c : Channels) (amp : Fin 8)
    (i j : Fin 4) (s t : Bool) (hij : i ≠ j) :
    ∃ amp', controlledReflection g (active c) (root i j s t) (encode g c amp) =
      encode g c amp' := by
  simpa [controlledReflection, (onWall_encode g c amp (active c)).mpr rfl] using
    wall_reflection g c amp i j s t hij

theorem controlledReflection_other_wall (g : Fin 3) (c : Channels) (amp : Fin 8)
    (b : Bool) (hb : active c ≠ b) (r : Wt) :
    controlledReflection g b r (encode g c amp) = encode g c amp := by
  have h : onWall g b (encode g c amp) ≠ true := fun h => hb ((onWall_encode g c amp b).mp h)
  simp [controlledReflection, h]

/-- The same untagged root can be active in one generation and static in another. -/
theorem no_root_only_wall_readout (read : Wt × Wt → Bool)
    (correct : ∀ g c amp, read (encode g c amp) = active c) : False := by
  let left : Channels := .inl (0, 0)
  let right : Channels := .inr (.inl (0, 0))
  have h : encode 0 left 2 = encode 1 right 2 := by decide +kernel
  have hleft : read (encode 0 left 2) = true := correct 0 left 2
  have hright : read (encode 1 right 2) = false := correct 1 right 2
  rw [h, hright] at hleft
  contradiction

/-- Forward triality crosses from the static wall to the active wall. -/
theorem crossing_encode (g : Fin 3) (c : Channels) (amp : Fin 8) (hc : active c = false) :
    crossing (encode g c amp) = encode g (opposite c) amp := by
  have hop : active (opposite c) = true := by rw [opposite_active, hc]; rfl
  have hx : g + 1 + 1 = g - 1 := by revert g; decide +kernel
  simp [encode, place, crossing, hc, hop, wallClass, opposite_label, frame_succ, hx]

theorem runCrossing_encode (g : Fin 3) (c : Channels) (amp : Fin 8)
    (hc : active c = false) :
    runCrossing (encode g c amp) = encode g (opposite c) amp := by
  rw [← crossing_encode g c amp hc]
  obtain ⟨a, b, h⟩ := encode_glued g c amp
  rw [h, crossing_word_glued]

/-- The exact crossing word sends the static neutral slot to the active
neutral channel with the same amplitude index. -/
theorem runCrossing_neutral (g : Fin 3) (amp : Fin 8) :
    runCrossing (encode g (.inr (.inr (.inr 0))) amp) =
      encode g (.inr (.inr (.inl 0))) amp :=
  runCrossing_encode g _ amp rfl

/-- The two lepton carriers with positive sign are the only protocol mismatch. -/
theorem crossing_preserves_protocol_iff : ∀ c : Channels,
    baseProtocol (opposite c) = baseProtocol c ↔ labelIndex c ≠ 0 := by
  decide +kernel

/-- Even a different wall exchange cannot carry the neutrino to a static
channel with that same base protocol. -/
theorem no_protocol_preserving_wall_exchange (f : Channels → Channels)
    (exchanges : ∀ c, active (f c) = !active c)
    (preserves : ∀ c, baseProtocol (f c) = baseProtocol c) : False := by
  let nu : Channels := .inr (.inr (.inl 0))
  have h : ∀ c : Channels, baseProtocol c = some .neutrino → active c = true := by
    decide +kernel
  have hnu : active (f nu) = true := h _ (preserves nu)
  have hstatic : active (f nu) = false := exchanges nu
  rw [hnu] at hstatic
  contradiction

end PMElementaryParticles.ControlledGluedRegister
