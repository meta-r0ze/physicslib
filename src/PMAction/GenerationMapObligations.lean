import PMAction.GenerationOrientation
import PMAction.FiniteEncoding

/-!
# What the MAP must retain for the existing glue-class moves

A task-facing retained code must give the same answer to each required future
move query whenever its code values agree. On the full six-state `IsGen` domain,
matched translations require exactly the omitted-class label. Single-wall move
queries distinguish both orientations too. These are obligations conditional on
the stated state domain and query family, not admission of those moves, an SM
identification, or permission to erase other conserved information.

The orientation coding is coherent and isometric. Retaining these distinctions
therefore does not itself require measurement or dephasing of a class reference.
The pair's omitted-class label is not identified with a reference carrier's class.
-/
noncomputable section
namespace PMAction.GenerationMapObligations
open GenerationSector Matrix

/-- The correctness condition of a retained MAP for a supplied future task. -/
def Supports {S Q R : Type*} (record : S → R) (test : S → Q → Prop) : Prop :=
  ∀ s t, record s = record t → ∀ q, test s q ↔ test t q

/-- Any actual decoder gives the required consistency condition. -/
theorem supports_of_decoder {S Q R : Type*} (record : S → R) (test : S → Q → Prop)
    (read : R → Q → Prop) (h : ∀ s q, read (record s) q ↔ test s q) :
    Supports record test := by
  intro s t he q
  rw [← h s q, ← h t q, he]

abbrev State := {p : Glue × Glue // IsGen p.1 p.2}
abbrev Label := {a : Glue // a ≠ 0}

def label (s : State) : Glue := s.val.1 + s.val.2

lemma label_nonzero (s : State) : label s ≠ 0 := by
  have h : ∀ b c : Glue, IsGen b c → b + c ≠ 0 := by decide +kernel
  exact h _ _ s.property

def labelCode (s : State) : Label := ⟨label s, label_nonzero s⟩

/-- A matched E8-class translation is tested against the kept pair domain. -/
def glueKeeps (s : State) (a : Glue) : Prop := IsGen (s.val.1 + a) (s.val.2 + a)

/-- Which of the two wall shifts is proposed is part of the task input. -/
def wallKeeps (s : State) (q : Bool × Glue) : Prop :=
  if q.1 then IsGen (s.val.1 + q.2) s.val.2 else IsGen s.val.1 (s.val.2 + q.2)

/-- Zero-glue moves leave the pair domain unchanged, so this restricted task
needs no pair label in its task-facing code. Other state information is not erased. -/
theorem root_only_map_suffices : Supports (fun _ : State => ())
    (fun s (_ : Bool × Fin 4) => glueKeeps s 0) := by
  intro s t he q
  have hs : glueKeeps s 0 := by simpa [glueKeeps] using s.property
  have ht : glueKeeps t 0 := by simpa [glueKeeps] using t.property
  exact ⟨fun _ => ht, fun _ => hs⟩

/-- The existing matched-translation menu identifies exactly the omitted label. -/
theorem glue_menu_iff (s t : State) :
    (∀ a, glueKeeps s a ↔ glueKeeps t a) ↔ label s = label t := by
  constructor
  · intro h
    have hs : glueKeeps s (label s) :=
      (glue_keeps_iff _ _ _ s.property).mpr (Or.inr rfl)
    have ht := (h (label s)).mp hs
    rcases (glue_keeps_iff _ _ _ t.property).mp ht with hz | he
    · exact False.elim (label_nonzero s hz)
    · exact he
  · intro h a
    change IsGen _ _ ↔ IsGen _ _
    rw [glue_keeps_iff _ _ _ s.property, glue_keeps_iff _ _ _ t.property]
    change (a = 0 ∨ a = label s) ↔ (a = 0 ∨ a = label t)
    rw [h]

/-- If both wall-query families are required, no two ordered pair states can alias. -/
theorem wall_menu_iff (s t : State) :
    (∀ q, wallKeeps s q ↔ wallKeeps t q) ↔ s = t := by
  constructor
  · intro h
    have hs1 : wallKeeps s (true,s.val.2) :=
      (shift_keeps_iff _ _ _ s.property s.property.2.1).mpr rfl
    have hs2 : wallKeeps s (false,s.val.1) :=
      (shift2_keeps_iff _ _ _ s.property s.property.1).1.mpr rfl
    have ht1 := (h (true,s.val.2)).mp hs1
    have ht2 := (h (false,s.val.1)).mp hs2
    have hc : s.val.2 = t.val.2 :=
      (shift_keeps_iff _ _ _ t.property s.property.2.1).mp ht1
    have hb : s.val.1 = t.val.1 :=
      (shift2_keeps_iff _ _ _ t.property s.property.1).1.mp ht2
    exact Subtype.ext (Prod.ext hb hc)
  · rintro rfl q; rfl

/-- Label-preserving translations plus moves on just the reference wall.
No access to the other wall's move menu is required. -/
def referenceKeeps (s : State) : Glue ⊕ Glue → Prop :=
  Sum.elim (glueKeeps s) (fun a => wallKeeps s (true,a))

theorem reference_menu_iff (s t : State) :
    (∀ q, referenceKeeps s q ↔ referenceKeeps t q) ↔ s = t := by
  constructor
  · intro h
    have hl := (glue_menu_iff s t).mp (fun a => h (.inl a))
    have hs : referenceKeeps s (.inr s.val.2) :=
      (shift_keeps_iff _ _ _ s.property s.property.2.1).mpr rfl
    have ht := (h (.inr s.val.2)).mp hs
    have hc : s.val.2 = t.val.2 :=
      (shift_keeps_iff _ _ _ t.property s.property.2.1).mp ht
    change s.val.1 + s.val.2 = t.val.1 + t.val.2 at hl
    rw [hc] at hl
    exact Subtype.ext (Prod.ext (add_right_cancel hl) hc)
  · rintro rfl q; rfl

theorem reference_support_iff {R : Type*} (record : State → R) :
    Supports record referenceKeeps ↔ Function.Injective record := by
  constructor
  · intro h s t he
    exact (reference_menu_iff s t).mp (h s t he)
  · intro h s t he
    exact (reference_menu_iff s t).mpr (h he)

theorem glue_support_iff {R : Type*} (record : State → R) :
    Supports record glueKeeps ↔ ∀ s t, record s = record t → label s = label t := by
  constructor
  · intro h s t he
    exact (glue_menu_iff s t).mp (h s t he)
  · intro h s t he
    exact (glue_menu_iff s t).mpr (h s t he)

theorem wall_support_iff {R : Type*} (record : State → R) :
    Supports record wallKeeps ↔ Function.Injective record := by
  constructor
  · intro h s t he
    exact (wall_menu_iff s t).mp (h s t he)
  · intro h s t he
    exact (wall_menu_iff s t).mpr (h he)

theorem label_suffices_for_glue : Supports labelCode glueKeeps := by
  apply (glue_support_iff labelCode).mpr
  intro s t h
  exact congrArg Subtype.val h

theorem state_card : Fintype.card State = 6 := by
  simpa only [State, Fintype.card_subtype] using gen_count

theorem label_card : Fintype.card Label = 3 := by decide +kernel

theorem label_surjective : Function.Surjective labelCode := by
  unfold Function.Surjective
  decide +kernel

/-- Three distinct task-facing codes are necessary for all matched translations. -/
theorem glue_record_bound {R : Type*} [Fintype R] (record : State → R)
    (h : Supports record glueKeeps) : 3 ≤ Fintype.card R := by
  classical
  let rep := Function.surjInv label_surjective
  have hi : Function.Injective (fun c => record (rep c)) := by
    intro c d he
    have hl := (glue_support_iff record).mp h _ _ he
    have hh : labelCode (rep c) = labelCode (rep d) := Subtype.ext hl
    simpa [rep, Function.surjInv_eq] using hh
  simpa only [label_card] using Fintype.card_le_of_injective _ hi

/-- Six distinct codes are necessary when all wall queries must be answered. -/
theorem wall_record_bound {R : Type*} [Fintype R] (record : State → R)
    (h : Supports record wallKeeps) : 6 ≤ Fintype.card R := by
  simpa only [state_card] using Fintype.card_le_of_injective record
    ((wall_support_iff record).mp h)

/-- Label plus reference-wall questions already require both orientations. -/
theorem reference_record_bound {R : Type*} [Fintype R] (record : State → R)
    (h : Supports record referenceKeeps) : 6 ≤ Fintype.card R := by
  simpa only [state_card] using Fintype.card_le_of_injective record
    ((reference_support_iff record).mp h)

def swap (s : State) : State :=
  ⟨(s.val.2,s.val.1), s.property.2.1, s.property.1, Ne.symm s.property.2.2⟩

theorem swap_same_label (s : State) : labelCode (swap s) = labelCode s := by
  apply Subtype.ext
  exact add_comm _ _

theorem swap_ne (s : State) : swap s ≠ s := by
  intro h
  have he := congrArg (fun t : State => t.val.1) h
  exact s.property.2.2 he.symm

/-- The lost orientation changes a concrete future wall-move answer. -/
theorem swap_changes_wall_query (s : State) :
    wallKeeps s (true,s.val.2) ∧ ¬wallKeeps (swap s) (true,s.val.2) := by
  constructor
  · exact (shift_keeps_iff _ _ _ s.property s.property.2.1).mpr rfl
  · intro h
    have he := (shift_keeps_iff _ _ _ (swap s).property s.property.2.1).mp h
    exact s.property.2.2 he.symm

theorem label_does_not_suffice_for_walls : ¬Supports labelCode wallKeeps := by
  intro h
  let s : State := ⟨((1,0),(0,1)), by decide +kernel⟩
  exact swap_ne s ((wall_support_iff labelCode).mp h (swap_same_label s))

/-! ## Coherent storage of label and orientation, without a preferred orientation -/

def orientedPair (e : Fin 3 → Glue) (p : Fin 3 × Bool) : Glue × Glue :=
  if p.2 then (e (p.1 - 1),e (p.1 + 1)) else (e (p.1 + 1),e (p.1 - 1))

theorem orientation_codes_complete : ∀ e : Fin 3 → Glue, GenerationOrientation.Good e →
    ∀ s : Glue × Glue, IsGen s.1 s.2 ↔ ∃! p : Fin 3 × Bool, orientedPair e p = s := by
  unfold ExistsUnique
  decide +kernel

theorem oriented_valid (e : Fin 3 → Glue) (he : GenerationOrientation.Good e)
    (p : Fin 3 × Bool) : IsGen (orientedPair e p).1 (orientedPair e p).2 := by
  have h := GenerationOrientation.type_is_gen e he p.1
  rcases p with ⟨g,b⟩
  cases b
  · exact h
  · exact ⟨h.2.1,h.1,Ne.symm h.2.2⟩

theorem oriented_injective : ∀ e : Fin 3 → Glue, GenerationOrientation.Good e →
    Function.Injective (orientedPair e) := by
  unfold Function.Injective
  decide +kernel

def orientedState (e : Fin 3 → Glue) (he : GenerationOrientation.Good e)
    (p : Fin 3 × Bool) : State := ⟨orientedPair e p, oriented_valid e he p⟩

theorem oriented_bijective (e : Fin 3 → Glue) (he : GenerationOrientation.Good e) :
    Function.Bijective (orientedState e he) := by
  constructor
  · intro p q h
    exact oriented_injective e he (congrArg Subtype.val h)
  · intro s
    obtain ⟨p,hp,hu⟩ := (orientation_codes_complete e he s.val).mp s.property
    exact ⟨p,Subtype.ext hp⟩

/-- A complete task-facing code consisting of label and orientation. -/
def orientationCode (e : Fin 3 → Glue) (he : GenerationOrientation.Good e) :
    State ≃ (Fin 3 × Bool) := (Equiv.ofBijective (orientedState e he) (oriented_bijective e he)).symm

theorem orientation_code_supports (e : Fin 3 → Glue) (he : GenerationOrientation.Good e) :
    Supports (orientationCode e he) referenceKeeps :=
  (reference_support_iff _).mpr (orientationCode e he).injective

def orientationEmbedding (e : Fin 3 → Glue) (he : GenerationOrientation.Good e) :
    Matrix State (Fin 3 × Bool) ℂ := FiniteEncoding.matrix (orientedState e he)

/-- Label plus orientation can be retained coherently: MAP retention is not measurement. -/
theorem orientation_isometry (e : Fin 3 → Glue) (he : GenerationOrientation.Good e) :
    (orientationEmbedding e he)ᴴ * orientationEmbedding e he = 1 :=
  FiniteEncoding.isometry _ (oriented_bijective e he).1

/-- Exchange of the two occupied classes on the full ordered-pair domain. -/
def swapEquiv : Equiv.Perm State where
  toFun := swap
  invFun := swap
  left_inv s := by apply Subtype.ext; rfl
  right_inv s := by apply Subtype.ext; rfl

def flipOrientation : Equiv.Perm (Fin 3 × Bool) where
  toFun p := (p.1,!p.2)
  invFun p := (p.1,!p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Pair exchange flips the orientation bit and preserves the label, for every
identification of the three indices with the nonzero glue classes. -/
theorem swap_orientation (e : Fin 3 → Glue) (he : GenerationOrientation.Good e)
    (p : Fin 3 × Bool) :
    swapEquiv (orientedState e he p) = orientedState e he (flipOrientation p) := by
  apply Subtype.ext
  rcases p with ⟨g,b⟩
  cases b <;> rfl

/-- Exact coherent two-channel action. This identifies pair exchange, not a
selected weak current, and assumes the full ordered-pair domain. -/
theorem orientation_flip_readout (e : Fin 3 → Glue) (he : GenerationOrientation.Good e) :
    swapEquiv.permMatrix ℂ * orientationEmbedding e he =
      orientationEmbedding e he * flipOrientation.permMatrix ℂ :=
  FiniteEncoding.intertwining (orientedState e he) flipOrientation swapEquiv
    (swap_orientation e he)

end PMAction.GenerationMapObligations
