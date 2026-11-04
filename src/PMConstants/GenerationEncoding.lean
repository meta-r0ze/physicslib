import PMConstants.Generations
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Glue-class pairs versus distinguishable generation states

Three unordered pairs are three possible sixteen-carrier packets. They are not
three disjoint native carrier sets at one site: every carrier appears in two
packets. This module keeps the omitted-class distinction instead of silently
discarding it. The resulting 48 labels have an exact encoding as the actual
24 class/carrier labels and one binary tag. The tag may be implemented by a
protocol history, location or another state factor, but none is selected here.

Likewise `Generations.same_class_loses` is a statement about the vector-only
readout. Equal-class packets retain all distinctions if their wall tag is kept.
Conservation alone therefore does not exclude them. Neither construction here
is a physical update law or a new admissible primitive event.
-/

noncomputable section
namespace PMConstants.GenerationEncoding
open PMAction.CarrierEvents PMAction.CarrierCost

/-- All actual minimal carriers in the three nontrivial glue classes. -/
abbrev Native := Σ c : Fin 3, Carrier c

/-- A generation is labelled by the class it omits; its occupied classes differ from it. -/
abbrev Generation (g : Fin 3) := Σ c : {c : Fin 3 // c ≠ g}, Carrier c.val

/-- A native carrier, together with which of its two compatible packets it belongs to. -/
abbrev Mode := Σ u : Native, {g : Fin 3 // g ≠ u.1}

def occupiedClasses (g : Fin 3) : Finset (Fin 3) := Finset.univ.erase g

/-- Complete classification within the stated unordered, distinct-class-pair contract. -/
theorem pair_classification : ∀ s : Finset (Fin 3), s.card = 2 →
    ∃! g : Fin 3, occupiedClasses g = s := by
  simp only [ExistsUnique]
  decide

theorem pair_types_three : Fintype.card {s : Finset (Fin 3) // s.card = 2} = 3 := by
  decide

/-- This excludes a fourth pair type, not a fourth arbitrary composite protocol. -/
theorem no_fourth_pair_type : ¬ ∃ f : Fin 4 → {s : Finset (Fin 3) // s.card = 2},
    Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, pair_types_three] at h
  omega

def forget (m : Mode) : Native := m.1

def nativeVector (u : Native) : Fin 4 → ℤ := vector u.2

/-- The 24 native labels really are distinct substrate vectors, not duplicate labels. -/
theorem native_vector_injective : Function.Injective nativeVector := by
  rintro ⟨c, v⟩ ⟨d, w⟩ h
  have hclass : classLabel c = classLabel d := v.2.1.symm.trans
    ((congrArg PMSubstrate.Channels.glueClass h).trans w.2.1)
  have hcd : c = d := Fin.ext (by simpa [classLabel] using hclass)
  subst d
  have hvw : v = w := vector_injective c h
  subst w
  rfl

theorem native_card : Fintype.card Native = 24 := by
  simp [Native, Fintype.card_sigma, carrier_card]

theorem generation_card (g : Fin 3) : Fintype.card (Generation g) = 16 := by
  have hc : Fintype.card {c : Fin 3 // c ≠ g} = 2 := by
    exact (Fintype.card_congr (finSuccAboveEquiv g)).symm
  simp [Generation, Fintype.card_sigma, carrier_card, hc]

/-- The modes are exactly the disjoint union of the three packet possibilities,
when their generation distinctions are retained. -/
def bundle : (Σ g : Fin 3, Generation g) ≃ Mode where
  toFun m := ⟨⟨m.2.1.val, m.2.2⟩, ⟨m.1, Ne.symm m.2.1.property⟩⟩
  invFun m := ⟨m.2.val, ⟨⟨m.1.1, Ne.symm m.2.property⟩, m.1.2⟩⟩
  left_inv m := by rcases m with ⟨g, ⟨⟨c, h⟩, v⟩⟩; rfl
  right_inv m := by rcases m with ⟨⟨c, v⟩, ⟨g, h⟩⟩; rfl

/-- Exact reversible storage, retaining a native carrier and one binary distinction.
The order convention in `finSuccAboveEquiv` is just a coding convention. -/
def tagged : Mode ≃ Native × Fin 2 where
  toFun m := (m.1, (finSuccAboveEquiv m.1.1).symm m.2)
  invFun p := ⟨p.1, finSuccAboveEquiv p.1.1 p.2⟩
  left_inv m := by cases m; simp
  right_inv p := by cases p; simp

theorem mode_card : Fintype.card Mode = 48 := by
  rw [Fintype.card_congr tagged, Fintype.card_prod, native_card, Fintype.card_fin]

/-- The binary encoding works on arbitrary coherent amplitudes, not only labels.
It is a change of representation; its existence does not price a physical gate. -/
def amplitudes : (Mode → ℂ) ≃ₗ[ℂ] (Native × Fin 2 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ tagged.symm

/-- The encoding preserves the complete complex pairing, including coherences. -/
theorem amplitude_pairing (ψ φ : Mode → ℂ) :
    ∑ p, star (amplitudes ψ p) * amplitudes φ p = ∑ m, star (ψ m) * φ m := by
  change (∑ p, star (ψ (tagged.symm p)) * φ (tagged.symm p)) = _
  exact Equiv.sum_comp tagged.symm (fun m => star (ψ m) * φ m)

/-- Every fixed native carrier occurs in exactly two generation-labelled modes. -/
def fibre (u : Native) : {m : Mode // forget m = u} ≃ Fin 2 where
  toFun m := (finSuccAboveEquiv u.1).symm ⟨m.1.2.val, by
    have he : m.1.1 = u := m.2
    intro h
    exact m.1.2.property (h.trans (congrArg Sigma.fst he).symm)⟩
  invFun b := ⟨tagged.symm (u, b), rfl⟩
  left_inv m := by
    rcases m with ⟨⟨u', g⟩, h⟩
    change u' = u at h
    subst u'
    simp [tagged]
  right_inv b := by simp [tagged]

theorem fibre_card (u : Native) : Fintype.card {m : Mode // forget m = u} = 2 := by
  simpa using Fintype.card_congr (fibre u)

/-- No encoding of all 48 distinguishable modes into only the 24 native labels
can preserve distinctions at a single site. Additional history/sites are not excluded. -/
theorem no_native_encoding : ¬ ∃ f : Mode → Native, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  rw [mode_card, native_card] at h
  omega

theorem forget_not_injective : ¬ Function.Injective forget := by
  intro h
  exact no_native_encoding ⟨forget, h⟩

/-- The obstruction also holds for coherent amplitudes, provided their encoding
is linear. It is a 48-versus-24 complex dimension bound, not an argument from
the set cardinality of a continuous amplitude space. -/
theorem no_linear_native_encoding :
    ¬ ∃ f : (Mode → ℂ) →ₗ[ℂ] (Native → ℂ), Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simp only [Module.finrank_pi] at h
  rw [mode_card, native_card] at h
  omega

/-- Any extra finite tag paired with a native carrier needs at least two values.
The exact binary witness is `tagged`; this is a capacity bound, not a toll price. -/
theorem tag_minimum {T : Type*} [Fintype T] (f : Mode → Native × T)
    (hf : Function.Injective f) : 2 ≤ Fintype.card T := by
  have h := Fintype.card_le_of_injective f hf
  rw [mode_card, Fintype.card_prod, native_card] at h
  omega

/-- An equal-class packet is fully distinguishable when the wall label is kept.
The vector-only collision theorem does not exclude this tagged state space. -/
def equalClassTagged (c : Fin 3) : Packet c c ≃ Bool × Carrier c where
  toFun := Sum.elim (fun v => (false, v)) (fun v => (true, v))
  invFun p := if p.1 then Sum.inr p.2 else Sum.inl p.2
  left_inv v := by cases v <;> rfl
  right_inv p := by rcases p with ⟨b, v⟩; cases b <;> rfl

theorem equal_class_boundary (c : Fin 3) :
    ¬ Function.Injective (@packetVector c c) ∧
      Function.Injective (equalClassTagged c) :=
  ⟨Generations.same_class_loses c, (equalClassTagged c).injective⟩

end PMConstants.GenerationEncoding
