import PMConstants.GenerationEncoding
import PMAction.SubstrateWeylRoots
import PMAction.FiniteEncoding

/-!
# A retained-carrier realization of the generation distinction

`GenerationEncoding` requires one binary distinction beyond a single bare
minimal carrier if all three pair types are to remain distinguishable. A second
actual carrier can hold it: record a carrier in the other occupied glue class.
The two observed classes determine the omitted class exactly. No new kind of
substrate label is needed for this representation.

Reference carriers, their preparation, record location and the dynamics updating
this history remain inputs. This is not a derivation of a generation interaction,
a free record supply or the independent three-generation Hilbert space.
-/

noncomputable section
namespace PMConstants.GenerationHistory
open GenerationEncoding PMAction.CarrierEvents
open Classical Matrix

/-- The third class: distinct labels in `Fin 3` sum to zero modulo three. -/
def third (a b : Fin 3) : Fin 3 := -a - b

theorem third_properties : ∀ a b : Fin 3, a ≠ b →
    third a b ≠ a ∧ third a b ≠ b ∧ third a (third a b) = b := by decide

/-- Two retained actual carriers in distinct glue classes, with live/record order retained. -/
abbrev History := {p : Native × Native // p.1.1 ≠ p.2.1}

/-- The omitted class is determined by the live and record classes. -/
def read (h : History) : Mode :=
  ⟨h.val.1, ⟨third h.val.1.1 h.val.2.1,
    ((third_properties _ _ h.property).1)⟩⟩

/-- Store the missing binary distinction using a supplied reference in the
other occupied class. Its value is not selected or given zero preparation cost. -/
def remember (reference : ∀ c : Fin 3, Carrier c) (m : Mode) : History :=
  ⟨(m.1, ⟨third m.1.1 m.2.val, reference (third m.1.1 m.2.val)⟩),
    Ne.symm (third_properties _ _ (Ne.symm m.2.property)).1⟩

/-- Keeping the actual companion record recovers every generation/carrier distinction. -/
theorem read_remember (reference : ∀ c : Fin 3, Carrier c) (m : Mode) :
    read (remember reference m) = m := by
  rcases m with ⟨⟨c, v⟩, ⟨g, h⟩⟩
  have ht := (third_properties c g (Ne.symm h)).2.2
  simp only [read, remember]
  congr 1
  exact Subtype.ext ht

theorem remember_injective (reference : ∀ c : Fin 3, Carrier c) :
    Function.Injective (remember reference) :=
  Function.LeftInverse.injective (read_remember reference)

/-- Sparse coherent embedding into actual two-carrier history states. -/
def embedding (reference : ∀ c : Fin 3, Carrier c) : Matrix History Mode ℂ :=
  PMAction.FiniteEncoding.matrix (remember reference)

/-- All generation amplitudes, including their coherences, are retained. -/
theorem isometry (reference : ∀ c : Fin 3, Carrier c) :
    (embedding reference)ᴴ * embedding reference = 1 :=
  PMAction.FiniteEncoding.isometry _ (remember_injective reference)

theorem encoded_coordinate (reference : ∀ c : Fin 3, Carrier c)
    (ψ : Mode → ℂ) (m : Mode) :
    (embedding reference *ᵥ ψ) (remember reference m) = ψ m :=
  PMAction.FiniteEncoding.coordinate _ (remember_injective reference) ψ m

theorem coherent_pairing (reference : ∀ c : Fin 3, Carrier c) (ψ φ : Mode → ℂ) :
    star (embedding reference *ᵥ ψ) ⬝ᵥ (embedding reference *ᵥ φ) = star ψ ⬝ᵥ φ :=
  PMAction.FiniteEncoding.pairing _ (remember_injective reference) ψ φ

/-- Forgetting the record recovers exactly the original bare native carrier. -/
theorem live_unchanged (reference : ∀ c : Fin 3, Carrier c) (m : Mode) :
    (remember reference m).val.1 = forget m := rfl

/-- The two physical carrier classes really are the two classes of this pair type. -/
theorem occupied_pair (reference : ∀ c : Fin 3, Carrier c) (m : Mode) :
    {(remember reference m).val.1.1, (remember reference m).val.2.1} =
      occupiedClasses m.2.val := by
  have h : ∀ c g : Fin 3, g ≠ c →
      ({c, third c g} : Finset (Fin 3)) = occupiedClasses g := by decide
  exact h m.1.1 m.2.val m.2.property

/-- Independent class-preserving carrier permutations on live and record fields.
No generation label is erased. The carrier permutations can be actual native roots. -/
def act (f g : ∀ c : Fin 3, Equiv.Perm (Carrier c)) : Equiv.Perm History where
  toFun h := ⟨(⟨h.val.1.1, f _ h.val.1.2⟩, ⟨h.val.2.1, g _ h.val.2.2⟩), h.property⟩
  invFun h := ⟨(⟨h.val.1.1, (f _).symm h.val.1.2⟩,
    ⟨h.val.2.1, (g _).symm h.val.2.2⟩), h.property⟩
  left_inv h := by simp only [Equiv.symm_apply_apply]
  right_inv h := by simp only [Equiv.apply_symm_apply]

theorem act_preserves_generation (f g : ∀ c : Fin 3, Equiv.Perm (Carrier c))
    (h : History) : (read (act f g h)).2.val = (read h).2.val := rfl

/-- One simple-root carrier step, on one of the two retained fields.
`SubstrateWeylRoots` certifies these roots in the actual E8 embedding.
This gate set is not asserted to exhaust the E8 substrate operations. -/
def rootGate (live : Bool) (j : Fin 4) : Equiv.Perm History :=
  act (fun c => if live then PMAction.CarrierWeyl.simple c j else 1)
    (fun c => if live then 1 else PMAction.CarrierWeyl.simple c j)

def run (word : List (Bool × Fin 4)) : Equiv.Perm History :=
  (word.map (fun p => rootGate p.1 p.2)).prod

/-- Every finite word in this native within-class gate set preserves the pair type.
Thus this retained-history realization alone supplies no generation mixing. -/
theorem root_words_preserve_generation (word : List (Bool × Fin 4)) (h : History) :
    (read (run word h)).2.val = (read h).2.val := by
  induction word with
  | nil => rfl
  | cons p word ih =>
    change (read (rootGate p.1 p.2 (run word h))).2.val = _
    exact (act_preserves_generation _ _ _).trans ih

/-- The coherent permutation matrices have no cross-generation entries either.
This concerns the specified within-class gate set, not all possible triality or
relational interactions. -/
theorem root_word_block (word : List (Bool × Fin 4)) (h k : History)
    (hne : (read h).2.val ≠ (read k).2.val) :
    (run word).permMatrix ℂ h k = 0 := by
  have hk : run word h ≠ k := by
    intro he
    apply hne
    exact (root_words_preserve_generation word h).symm.trans
      (congrArg (fun z => (read z).2.val) he)
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hk]

end PMConstants.GenerationHistory
