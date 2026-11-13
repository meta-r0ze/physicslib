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

* `singlet_least`: on a carrier that is a singlet of both non-abelian factors (the electron), any
  root event acts only through its phase, so the phase displacement is repaired by exactly one
  event.

* `event_inv`: a disturbance that is one event in a factor is undone by its inverse, one event in
  the same factor (a root reflection is its own inverse).
* `covering_least`: a maintained carrier's repair must cover every displacement its factors can
  produce (`Admissible`); the worst case displaces every charged factor, so the least covering
  budget is one event per charged non-abelian factor, at least one with a phase. This replaces
  the premise that a disturbance displaces exactly the charged factors.

The model counts each factor element as one event: a disturbance is one root event in a factor,
and `event_inv` undoes it with one.
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

omit [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] in
/-- **A singlet's phase is repaired by one root event.** On a carrier that is a singlet of both
non-abelian factors, a root event `(c, w)` of either factor acts only through the phase it carries.
So the singlet's phase displacement `p` is undone by one event, any root event carrying `p`, and
not by zero events. No phase-only event needs to exist. -/
theorem singlet_least (p : P) (hp : p ≠ 1) (r : Gc × Gw) (hr : r.1 = 1 ∨ r.2 = 1) :
    IsLeast {n | ∃ L : List (Gc × Gw × P), (∀ e ∈ L, IsEvent e) ∧
      (L.map fun e => e.2.2).prod = p ∧ L.length = n} 1 := by
  refine ⟨⟨[(r.1, r.2, p)], by simpa [IsEvent] using hr, by simp, rfl⟩, ?_⟩
  rintro n ⟨L, -, hprod, rfl⟩
  rcases L with _ | ⟨a, L⟩
  · exact absurd (by simpa using hprod.symm) hp
  · simp

omit [DecidableEq Gc] [DecidableEq Gw] [DecidableEq P] in
/-- **The undo of an event is an event.** A disturbance that is one event in one factor is undone
by its inverse, again one event in that factor (for a root reflection, the same reflection). -/
theorem event_inv (d : Gc × Gw × P) (hd : IsEvent d) : IsEvent d⁻¹ := by
  rcases hd with h | h
  · left; simp [h]
  · right; simp [h]

/-- The displacements a carrier's factors can produce: trivial in every factor it is not charged
under. -/
def Admissible (kc kw kp : Prop) (g : Gc × Gw × P) : Prop :=
  (¬ kc → g.1 = 1) ∧ (¬ kw → g.2.1 = 1) ∧ (¬ kp → g.2.2 = 1)

/-- A repair budget `n` covers a set of displacements if each has a repair of at most `n` events. -/
def Covers (S : Gc × Gw × P → Prop) (n : ℕ) : Prop :=
  ∀ g, S g → ∃ L : List (Gc × Gw × P), (∀ e ∈ L, IsEvent e) ∧ L.prod = g ∧ L.length ≤ n

/-- **Persistence: the least budget that repairs every displacement the factors can produce.**
A maintained carrier must be repaired against every displacement its factors can produce, so its
budget covers them all; the worst case displaces every charged factor, and the least covering
budget is one event per charged non-abelian factor, at least one if it carries a phase. -/
theorem covering_least (kc kw kp : Prop) [Decidable kc] [Decidable kw] [Decidable kp]
    (c₀ : Gc) (hc₀ : c₀ ≠ 1) (w₀ : Gw) (hw₀ : w₀ ≠ 1) (p₀ : P) (hp₀ : p₀ ≠ 1) :
    IsLeast {n | Covers (Admissible (Gc := Gc) (Gw := Gw) (P := P) kc kw kp) n}
      (max ((if kc then 1 else 0) + (if kw then 1 else 0)) (if kp then 1 else 0)) := by
  constructor
  · intro g hg
    obtain ⟨L, hL, hprod, hlen⟩ := events_attained g
    refine ⟨L, hL, hprod, ?_⟩
    rw [hlen]
    obtain ⟨h1, h2, h3⟩ := hg
    unfold need displaced
    by_cases a : kc <;> by_cases b : kw <;> by_cases c : kp <;>
      simp_all <;> (try split_ifs) <;> omega
  · intro n hn
    let g : Gc × Gw × P := (if kc then c₀ else 1, if kw then w₀ else 1, if kp then p₀ else 1)
    have hg : Admissible kc kw kp g := by
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [g, h]
    obtain ⟨L, hL, hprod, hlen⟩ := hn g hg
    have hge := events_ge L hL
    rw [hprod] at hge
    have hneed : need g = max ((if kc then 1 else 0) + (if kw then 1 else 0))
        (if kp then 1 else 0) := by
      unfold need displaced
      by_cases a : kc <;> by_cases b : kw <;> by_cases c : kp <;> simp [g, a, b, c, hc₀, hw₀, hp₀]
    omega

end PMAction.FactorRepair
