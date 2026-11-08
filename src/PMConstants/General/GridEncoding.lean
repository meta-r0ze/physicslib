import PMConstants.General.ReferenceCapacity
import PMSubstrate.E8Values
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! Clock-equivariant full-alphabet coding on the actual 4 × 43 phase grid.
Adapted from Claude's grid-sufficiency proof; the grid and update are imported
from ReferenceCapacity so necessity and sufficiency concern the same objects.
This is a choice-based existence result, with no encoding-cost or locality bound. -/
namespace PMConstants.General.ReferenceCapacity.GridEncoding
open Function
open PMConstants.General.ReferenceCapacity

variable {a : ℕ}
local notation "U" => (gridUpdate (a := a))

lemma iter_apply (n : ℕ) (w : Grid → Fin a) (x : Grid) :
    U^[n] w x = w (x.1, ((finRotate PMSubstrate.E8Values.Delta).symm)^[n] x.2) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, ih, iterate_succ_apply']
    rfl

lemma rot_period : ∀ t : Fin PMSubstrate.E8Values.Delta, ((finRotate PMSubstrate.E8Values.Delta).symm)^[43] t = t := by decide +kernel
lemma rot_to_zero : ∀ t : Fin PMSubstrate.E8Values.Delta, ((finRotate PMSubstrate.E8Values.Delta).symm)^[t.val] t = 0 := by decide +kernel
lemma rot_succ_val : ∀ t : Fin PMSubstrate.E8Values.Delta, (finRotate PMSubstrate.E8Values.Delta t).val = (t.val + 1) % 43 := by decide +kernel

lemma periodic (w : Grid → Fin a) : IsPeriodicPt U 43 w := by
  funext x; rw [iter_apply, rot_period]

/-- `43` is prime: a word not fixed by one step has exact period `43`. -/
lemma period_dvd {w : Grid → Fin a} (hw : U w ≠ w) {k : ℕ} (hk : U^[k] w = w) : 43 ∣ k := by
  have hmp : minimalPeriod U w = 43 := by
    rcases (Nat.prime_def.mp (by norm_num : Nat.Prime 43)).2 _ ((periodic w).minimalPeriod_dvd)
      with h | h
    · exfalso
      have hp := isPeriodicPt_minimalPeriod U w
      rw [h] at hp
      exact hw hp
    · exact h
  rw [← hmp]; exact IsPeriodicPt.minimalPeriod_dvd hk

lemma iter_comm (m n : ℕ) (w : Grid → Fin a) : U^[m] (U^[n] w) = U^[m+n] w := by
  rw [iterate_add_apply]

/-! Orbits of free words. -/
abbrev Free (a : ℕ) := {w : Grid → Fin a // gridUpdate w ≠ w}

def orbitSetoid (a : ℕ) : Setoid (Free a) where
  r w v := ∃ k : ℕ, (gridUpdate (a := a))^[k] w.1 = v.1
  iseqv := by
    refine ⟨fun w => ⟨0, rfl⟩, ?_, ?_⟩
    · rintro w v ⟨k, hk⟩
      refine ⟨43 - k % 43, ?_⟩
      rw [← hk, ← (periodic w.1).iterate_mod_apply, iter_comm]
      have := Nat.mod_lt k (by norm_num : 0 < 43)
      rw [show 43 - k % 43 + k % 43 = 43 by omega]
      exact periodic w.1
    · rintro w v u ⟨k, hk⟩ ⟨j, hj⟩
      exact ⟨j + k, by rw [← iter_comm, hk, hj]⟩

abbrev Orbits (a : ℕ) := Quotient (orbitSetoid a)

open Classical in
noncomputable instance : Fintype (Free a) := by unfold Free; infer_instance
open Classical in
noncomputable instance : Fintype (Orbits a) := by unfold Orbits; infer_instance

/-- Every free orbit has at most `43` elements: `card Free ≤ 43 · card Orbits`. -/
lemma free_le_orbits : Fintype.card (Free a) ≤ 43 * Fintype.card (Orbits a) := by
  classical
  have hex : ∀ w : Free a, ∃ k : Fin PMSubstrate.E8Values.Delta,
      U^[k.val] (Quotient.out (⟦w⟧ : Orbits a)).1 = w.1 := by
    intro w
    obtain ⟨k, hk⟩ := Quotient.mk_out (s := orbitSetoid a) w
    refine ⟨⟨k % 43, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simpa [(periodic _).iterate_mod_apply] using hk
  let f : Free a → Orbits a × Fin PMSubstrate.E8Values.Delta := fun w => (⟦w⟧, (hex w).choose)
  have hf : Injective f := by
    intro w v h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨hq, hk⟩ := h
    have hw := (hex w).choose_spec
    have hv := (hex v).choose_spec
    rw [hk] at hw
    rw [hq] at hw
    exact Subtype.ext (hw.symm.trans hv)
  have := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, mul_comm] using this

/-- Fixed words are phase-constant in each direction: at most `a^4` of them. -/
lemma fixed_le : Fintype.card {w : Grid → Fin a // U w = w} ≤ a ^ 4 := by
  classical
  let g : {w : Grid → Fin a // U w = w} → (Fin 4 → Fin a) := fun w d => w.1 (d, 0)
  have hg : Injective g := by
    intro w v h
    apply Subtype.ext; funext x
    have hw : U^[x.2.val] w.1 = w.1 := iterate_fixed w.2 _
    have hv : U^[x.2.val] v.1 = v.1 := iterate_fixed v.2 _
    rw [← hw, ← hv, iter_apply, iter_apply, rot_to_zero]
    exact congrFun h x.1
  simpa using Fintype.card_le_of_injective g hg

lemma words_le : a ^ 172 ≤ Fintype.card (Free a) + a ^ 4 := by
  classical
  have h := Fintype.card_subtype_compl (fun w : Grid → Fin a => U w = w)
  have hc : Fintype.card (Grid → Fin a) = a ^ 172 := by simp [Grid]
  have hF : Fintype.card (Free a) = Fintype.card {w : Grid → Fin a // ¬ U w = w} :=
    Fintype.card_congr (Equiv.refl _)
  have := fixed_le (a := a)
  have hle := Fintype.card_subtype_le (fun w : Grid → Fin a => U w = w)
  omega

lemma enough_orbits (ha : 173 ≤ a) : 4 * a ^ 171 ≤ Fintype.card (Orbits a) := by
  have h1 := words_le (a := a)
  have h2 := free_le_orbits (a := a)
  have h3 : a ^ 4 ≤ a ^ 171 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : a ^ 172 = a * a ^ 171 := by ring
  have h5 : 173 * a ^ 171 ≤ a * a ^ 171 := Nat.mul_le_mul_right _ ha
  omega

/-- **Sufficiency.** For `a ≥ 173` there is an injective encoder of every reference/payload
pair that commutes with the phase ticks. -/
theorem grid_one_slot_sufficient (ha : 173 ≤ a) :
    ∃ code : Grid × (Fin 171 → Fin a) → (Grid → Fin a), Injective code ∧
      ∀ o p, gridUpdate (code (o, p)) = code (gridTick o, p) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4 × (Fin 171 → Fin a)) (β := Orbits a)
    (by simpa [Fintype.card_prod] using enough_orbits ha)
  let base : Fin 4 × (Fin 171 → Fin a) → Free a := fun x => Quotient.out (e x)
  let code : Grid × (Fin 171 → Fin a) → (Grid → Fin a) :=
    fun op => U^[op.1.2.val] (base (op.1.1, op.2)).1
  refine ⟨code, ?_, ?_⟩
  · rintro ⟨⟨d, t⟩, p⟩ ⟨⟨d', s⟩, p'⟩ h
    simp only [code] at h
    -- bring both to the base of the first: apply `43 - t` more ticks
    have ht : t.val < 43 :=
      lt_of_lt_of_eq t.isLt PMSubstrate.E8Values.Delta_eq
    have h' := congrArg (U^[43 - t.val]) h
    rw [iter_comm, iter_comm, show 43 - t.val + t.val = 43 by omega, periodic] at h'
    -- same orbit, so same embedded class
    have hrel : orbitSetoid a (base (d', p')) (base (d, p)) := ⟨_, h'.symm⟩
    have hq : e (d', p') = e (d, p) := by
      have := Quotient.sound hrel
      simpa [base, Quotient.out_eq] using this
    have hx := e.injective hq
    simp only [Prod.mk.injEq] at hx
    rw [hx.1, hx.2] at h'
    -- exact period 43 forces equal phases
    have hd := period_dvd (base (d, p)).2 h'.symm
    have hs : s = t := by
      apply Fin.ext
      have hs2 : s.val < 43 :=
        lt_of_lt_of_eq s.2 PMSubstrate.E8Values.Delta_eq
      have ht2 : t.val < 43 :=
        lt_of_lt_of_eq t.2 PMSubstrate.E8Values.Delta_eq
      omega
    rw [hx.1, hx.2, hs]
  · rintro ⟨d, t⟩ p
    simp only [code, gridTick]
    rw [← iterate_succ_apply' U, rot_succ_val, (periodic _).iterate_mod_apply]

/-- The nonempty alphabet hypothesis excludes the vacuous empty-domain code at a = 0. -/
theorem grid_one_slot_iff (ha : 1 ≤ a) :
    (∃ code : Grid × (Fin 171 → Fin a) → (Grid → Fin a), Injective code ∧
      ∀ o p, gridUpdate (code (o, p)) = code (gridTick o, p)) ↔ 173 ≤ a := by
  constructor
  · rintro ⟨code, hinj, heq⟩
    exact grid_one_slot_requires_wider a ha code hinj heq
  · exact grid_one_slot_sufficient

end PMConstants.General.ReferenceCapacity.GridEncoding
