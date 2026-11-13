import PMConstants.GenerationEncoding

/-!
# Three packets on the two-wall carrier labels

The binary distinction in `GenerationEncoding` need not be new memory: there
are already two domain-wall sectors. A cyclic incidence convention places all
48 modes on wall × (the 24 minimal class/carrier labels), with one class per
wall in every generation. There are precisely two balanced incidence conventions,
related by exchanging the wall names.

This is an exact representation using all three classes in both walls. It does
not prove that the physical vacuum admits every such mode, identify the update,
or turn a sector-exchange symmetry into a quotient of physical states. In
particular it does not derive generation masses or mixing parameters.

**Why this realization.** The tag needs one bit. The walls already supply it, with exactly the
capacity needed (`encode`, `wall_native_card`); the companion-carrier history
(`GenerationHistory`) spends a second carrier per mode. Economy (no spare coordinate,
`PMSubstrate.FinalPremises.description_minimal`) takes the existing wall label.
`no_further_modes`: the 48 wall labels are then used exactly by the three generations, so an
equal-class packet has no room as a further state; no vector-faithful readout contract is needed
to exclude it.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMConstants.GenerationWalls
open GenerationEncoding

abbrev WallNative := Bool × Native

def side (g c : Fin 3) : Bool := decide (c = g + 1)

def omitted (b : Bool) (c : Fin 3) : Fin 3 := if b then c - 1 else c + 1

theorem decode_side : ∀ g c : Fin 3, g ≠ c → omitted (side g c) c = g := by decide

theorem side_decode : ∀ b c, side (omitted b c) c = b ∧ omitted b c ≠ c := by decide

/-- The wall factor already has exactly the necessary capacity. Every generation
uses one of its occupied classes on each wall, not two classes on the same wall. -/
def encode : Mode ≃ WallNative where
  toFun m := (side m.2.val m.1.1, m.1)
  invFun p := ⟨p.2, ⟨omitted p.1 p.2.1, (side_decode p.1 p.2.1).2⟩⟩
  left_inv m := by
    rcases m with ⟨u, ⟨g, h⟩⟩
    change (⟨u, ⟨omitted (side g u.1) u.1, _⟩⟩ : Mode) = ⟨u, ⟨g, h⟩⟩
    apply congrArg (fun q : {a : Fin 3 // a ≠ u.1} => (⟨u, q⟩ : Mode))
    exact Subtype.ext (decode_side g u.1 h)
  right_inv p := by
    rcases p with ⟨b, u⟩
    exact Prod.ext (side_decode b u.1).1 rfl

theorem wall_native_card : Fintype.card WallNative = 48 := by
  change Fintype.card (Bool × Native) = 48
  rw [Fintype.card_prod, native_card]
  norm_num

/-- Each packet has exactly one occupied class on either wall. -/
theorem one_class_per_wall : ∀ (g : Fin 3) (b : Bool),
    ∃! c : Fin 3, g ≠ c ∧ side g c = b := by
  simp only [ExistsUnique]
  decide

/-- The incidence convention preserves all amplitudes and their complex pairings. -/
def amplitudes : (Mode → ℂ) ≃ₗ[ℂ] (WallNative → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ encode.symm

theorem coherent_pairing (ψ φ : Mode → ℂ) :
    ∑ p, star (amplitudes ψ p) * amplitudes φ p = ∑ m, star (ψ m) * φ m := by
  change (∑ p, star (ψ (encode.symm p)) * φ (encode.symm p)) = _
  exact Equiv.sum_comp encode.symm (fun m => star (ψ m) * φ m)

/-- The six occupied generation/class incidences; unused diagonal entries are absent. -/
abbrev Incidence := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

def policy : Incidence → Bool := fun p => side p.val.1 p.val.2

def Balanced (p : Incidence → Bool) : Prop :=
  (∀ g : Fin 3, ∃! c : {c : Fin 3 // g ≠ c}, p ⟨(g, c.val), c.property⟩ = true) ∧
  (∀ c : Fin 3, ∃! g : {g : Fin 3 // g ≠ c}, p ⟨(g.val, c), g.property⟩ = true)

/-- The two possible balanced encodings differ only by exchanging the wall names.
This finite classification does not choose a physical chirality orientation. -/
theorem balanced_classification : ∀ p : Incidence → Bool,
    Balanced p ↔ p = policy ∨ p = fun i => !(policy i) := by
  simp only [Balanced, ExistsUnique]
  decide

/-- Exchange wall labels while keeping the actual class/carrier fixed. -/
def exchange : Equiv.Perm WallNative where
  toFun p := (!p.1, p.2)
  invFun p := (!p.1, p.2)
  left_inv p := by cases p with | mk b u => cases b <;> rfl
  right_inv p := by cases p with | mk b u => cases b <;> rfl

def exchangeMode : Equiv.Perm Mode := encode.trans (exchange.trans encode.symm)

theorem exchange_generation (m : Mode) :
    (exchangeMode m).2.val = omitted (!(side m.2.val m.1.1)) m.1.1 := rfl

/-- In this wall encoding, the wall exchange changes the packet type in a way
that depends on the occupied class. It cannot silently be treated as a wall
swap acting identically on an independent generation factor. -/
theorem exchange_not_generation_only : ¬ ∃ f : Fin 3 → Fin 3,
    ∀ g c : Fin 3, g ≠ c → omitted (!(side g c)) c = f g := by decide

/-- **No room for a further packet type on the walls.** The 48 wall-carrier labels are used
exactly by the three distinct-class generations (`encode` is a bijection), so no further mode
type, such as an equal-class packet, fits injectively beside them. -/
theorem no_further_modes (E : Type*) [Fintype E] [Nonempty E] :
    ¬ ∃ f : Mode ⊕ E → WallNative, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h1 := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sum, Fintype.card_congr encode] at h1
  have := Fintype.card_pos (α := E)
  omega

end PMConstants.GenerationWalls
