import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Order.Bounds.Basic

/-!
# Repair events in a product of gauge factors

A carrier's state is displaced in a colour factor `Gc`, a weak factor `Gw` and an abelian phase
`P`. A primitive event is a root event: the roots of a product algebra are the disjoint union of
each factor's roots, so a root event acts in **one** non-abelian factor (`IsEvent`). The abelian
factor has no roots; its phase rides on the amplitude of whatever event occurs, so an event may
carry any phase.

A repair is a word of events whose product undoes the displacement `g = (c, w, p)`.

* `colour_needs_event`, `weak_needs_event`: a nontrivial colour (weak) displacement needs a colour
  (weak) event in the word; `phase_needs_event`: a nontrivial phase needs a nonempty word.
* `events_ge` (Conservation): every repair has at least `need g` events, where `need g` is the
  number of displaced non-abelian factors, or `1` if only the phase is displaced.
* `events_attained`: one event per displaced factor, with the phase carried by one of them, is a
  repair of exactly that length.
* `repair_least` (Economy): the least repair length is `need g`.

Premises: a displacement in one factor is undone by one event of that factor (a disturbance is a
single root event, so its undo is one); and a phase-only displacement is repaired by one event
(the electron's case, the single remaining premise of `PMConstants.RootRepairRule`).
-/

namespace PMAction.FactorRepair

variable {Gc Gw P : Type*} [Group Gc] [Group Gw] [CommGroup P]
  [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P]

/-- An event acts in at most one non-abelian factor and carries a phase. -/
def IsEvent (e : Gc × Gw × P) : Prop := e.1 = 1 ∨ e.2.1 = 1

/-- Displaced non-abelian factors. -/
def displaced (g : Gc × Gw × P) : ℕ := (if g.1 ≠ 1 then 1 else 0) + (if g.2.1 ≠ 1 then 1 else 0)

/-- The least number of events a repair needs. -/
def need (g : Gc × Gw × P) : ℕ := max (displaced g) (if g.2.2 ≠ 1 then 1 else 0)

omit [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] in
lemma prod_fst (L : List (Gc × Gw × P)) : L.prod.1 = (L.map Prod.fst).prod :=
  (MonoidHom.fst Gc (Gw × P)).map_list_prod L

omit [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] in
lemma prod_snd_fst (L : List (Gc × Gw × P)) : L.prod.2.1 = (L.map fun e => e.2.1).prod := by
  have h := ((MonoidHom.fst Gw P).comp (MonoidHom.snd Gc (Gw × P))).map_list_prod L
  simpa [List.map_map, Function.comp_def] using h

omit [DecidableEq Gw] [DecidableEq P] in
/-- **A colour displacement needs a colour event.** -/
theorem colour_needs_event (L : List (Gc × Gw × P)) (h : L.prod.1 ≠ 1) : ∃ e ∈ L, e.1 ≠ 1 := by
  by_contra hn
  push Not at hn
  apply h
  rw [prod_fst]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact hn e he

omit [DecidableEq Gc] [DecidableEq P] in
/-- **A weak displacement needs a weak event.** -/
theorem weak_needs_event (L : List (Gc × Gw × P)) (h : L.prod.2.1 ≠ 1) :
    ∃ e ∈ L, e.2.1 ≠ 1 := by
  by_contra hn
  push Not at hn
  apply h
  rw [prod_snd_fst]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact hn e he

omit [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] in
/-- **A phase displacement needs some event.** -/
theorem phase_needs_event (L : List (Gc × Gw × P)) (h : L.prod.2.2 ≠ 1) : 1 ≤ L.length := by
  rcases L with _ | ⟨a, L⟩
  · simp at h
  · simp

omit [CommGroup P] [DecidableEq P] in
/-- No event acts in both non-abelian factors, so colour and weak events are counted apart. -/
lemma count_le (L : List (Gc × Gw × P)) (hL : ∀ e ∈ L, IsEvent e) :
    L.countP (fun e => e.1 ≠ 1) + L.countP (fun e => e.2.1 ≠ 1) ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := hL a List.mem_cons_self
    have ih' := ih fun e he => hL e (List.mem_cons_of_mem a he)
    simp only [List.countP_cons, List.length_cons]
    unfold IsEvent at ha
    rcases ha with h | h <;> simp [h] at ih' ⊢ <;> (try split_ifs) <;> omega

/-- **Conservation: every repair has at least `need g` events.** -/
theorem events_ge (L : List (Gc × Gw × P)) (hL : ∀ e ∈ L, IsEvent e) :
    need L.prod ≤ L.length := by
  have hc := count_le L hL
  have h1 : (if L.prod.1 ≠ 1 then 1 else 0) ≤ L.countP (fun e => e.1 ≠ 1) := by
    split_ifs with h
    · obtain ⟨e, he, hne⟩ := colour_needs_event L h
      have : L.countP (fun e => e.1 ≠ 1) ≠ 0 := fun h0 =>
        (List.countP_eq_zero.1 h0 e he) (by simpa using hne)
      omega
    · exact Nat.zero_le _
  have h2 : (if L.prod.2.1 ≠ 1 then 1 else 0) ≤ L.countP (fun e => e.2.1 ≠ 1) := by
    split_ifs with h
    · obtain ⟨e, he, hne⟩ := weak_needs_event L h
      have : L.countP (fun e => e.2.1 ≠ 1) ≠ 0 := fun h0 =>
        (List.countP_eq_zero.1 h0 e he) (by simpa using hne)
      omega
    · exact Nat.zero_le _
  have h3 : (if L.prod.2.2 ≠ 1 then 1 else 0) ≤ L.length := by
    split_ifs with h
    · exact phase_needs_event L h
    · exact Nat.zero_le _
  unfold need displaced
  omega

/-- **One event per displaced factor suffices.** -/
theorem events_attained (g : Gc × Gw × P) :
    ∃ L : List (Gc × Gw × P), (∀ e ∈ L, IsEvent e) ∧ L.prod = g ∧ L.length = need g := by
  obtain ⟨c, w, p⟩ := g
  by_cases hc : c = 1 <;> by_cases hw : w = 1 <;> by_cases hp : p = 1
  · exact ⟨[], by simp, by subst hc hw hp; rfl, by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(1, 1, p)], by simp [IsEvent], by simp [hc, hw], by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(1, w, p)], by simp [IsEvent], by simp [hc], by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(1, w, p)], by simp [IsEvent], by simp [hc], by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(c, 1, p)], by simp [IsEvent], by simp [hw], by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(c, 1, p)], by simp [IsEvent], by simp [hw], by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(c, 1, p), (1, w, 1)], by simp [IsEvent], by simp,
      by simp [need, displaced, hc, hw, hp]⟩
  · exact ⟨[(c, 1, p), (1, w, 1)], by simp [IsEvent], by simp,
      by simp [need, displaced, hc, hw, hp]⟩

/-- **Economy: the least repair has `need g` events.** -/
theorem repair_least (g : Gc × Gw × P) :
    IsLeast {n | ∃ L : List (Gc × Gw × P), (∀ e ∈ L, IsEvent e) ∧ L.prod = g ∧ L.length = n}
      (need g) := by
  refine ⟨events_attained g, ?_⟩
  rintro n ⟨L, hL, rfl, rfl⟩
  exact events_ge L hL

end PMAction.FactorRepair
