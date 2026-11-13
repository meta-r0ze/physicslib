import PMConstants.RequirementRows

/-!
# Why weak refreshes only the clock row: its events do not move

`RequirementRows.rows_assigned` needs weak to refresh no frame row but the reference's, and
`ReferenceMaintenanceLedger` shows Economy over the ledger weights alone does not force it: moving the
spatial rows to weak keeps the same total. This module gives the missing distinction from the factor
structure.

A frame row is a direction `μ` of the node, with `43` phase addresses along it (`RequirementRows`);
row `0` is time (the reference's axis), so its addresses are the node's own site at successive
ticks, and a spatial row's addresses lie at other sites, `k` steps along `μ`.

* An event acts in one factor (`PMAction.FactorRepair`). E8 is `D₄ ⊕ D₄`, spacetime and internal,
  and a root of one summand has no component in the other. Weak's events are internal: the weak
  action permutes internal carrier labels (`CarrierActions.weak`) and moves no site. So a word of
  weak events has zero spatial displacement (`internal_stays`); between ticks only the clock moves.
* `weak_covers_iff`: weak's own events, over any number of ticks, reach every address of row `μ`
  exactly when `μ` is the time row.
* `rows_from_locality`: so a refresh assignment in which weak refreshes a row only with its own
  events gives weak the clock row alone and hypercharge the three spatial rows: the premise of
  `rows_assigned`, now with the frame ledgers `43` and `129` (`frame_from_locality`).

Hypercharge differs because it has no events of its own: `u(1)` has no roots, and its phase rides
on whatever events occur (`FactorRepair`), including the spatial hops that transport the packet. So
it can cover the spatial rows without events of its own, and weak cannot without spatial events,
which are not weak's. The countermodel of `ReferenceMaintenanceLedger` prices rows but not this
reach.

* `weak_misses_wires`: a wire is a 1-cell between the node and a neighbour, displaced along a root
  (two nonzero coordinates, so at least one spatial); weak's own events never reach it either.

Premise: a sector refreshes an address only with its own events (or, for the abelian phase,
riding on events that occur). The payload resources sit at the node, so this argument does not
decide them.
-/

namespace PMConstants.WeakLocality
open RequirementRows

/-- The unit step along direction `μ`; `0` is time. -/
def e (μ : Fin 4) : Fin 4 → ℤ := fun i => if i = μ then 1 else 0

/-- Address `k` of frame row `μ`: `k` steps along `μ` from the node. -/
def address (μ : Fin 4) (k : ℕ) : Fin 4 → ℤ := (k : ℤ) • e μ

/-- **Internal events do not move.** After `t` ticks and a word of events with zero spacetime
displacement, the position is `t` steps along time. -/
theorem internal_stays (L : List (Fin 4 → ℤ)) (hL : ∀ d ∈ L, d = 0) (t : ℕ) :
    (t : ℤ) • e 0 + L.sum = (t : ℤ) • e 0 := by
  rw [List.sum_eq_zero hL, add_zero]

/-- Weak covers row `μ` if every one of its `43` addresses is reached by ticks and weak's own
(internal) events. -/
def WeakCovers (μ : Fin 4) : Prop :=
  ∀ k < 43, ∃ (t : ℕ) (L : List (Fin 4 → ℤ)), (∀ d ∈ L, d = 0) ∧
    (t : ℤ) • e 0 + L.sum = address μ k

/-- **Weak's own events reach exactly the time row.** -/
theorem weak_covers_iff (μ : Fin 4) : WeakCovers μ ↔ μ = 0 := by
  constructor
  · intro h
    by_contra hμ
    obtain ⟨t, L, hL, heq⟩ := h 1 (by norm_num)
    rw [internal_stays L hL t] at heq
    have := congrFun heq μ
    simp [address, e, hμ] at this
  · rintro rfl k _
    exact ⟨k, [], by simp, by simp [address]⟩

/-- **Weak refreshes the clock row alone.** If weak refreshes a row only with its own events, the
assignment of `rows_assigned` follows. -/
theorem rows_from_locality (f : Fin 4 → Sector) (hw : f 0 = .weak)
    (hcap : ∀ μ, f μ = .weak → WeakCovers μ) :
    ∀ r, f r = if r = 0 then .weak else .hyper :=
  rows_assigned f hw fun r h => (weak_covers_iff r).1 (hcap r h)

/-- **The frame ledgers `43` and `129` from locality.** -/
theorem frame_from_locality (f : Fin 4 → Sector) (hw : f 0 = .weak)
    (hcap : ∀ μ, f μ = .weak → WeakCovers μ) :
    (Finset.univ.filter fun r => f r = .weak).card * rowWeight = 43 ∧
      (Finset.univ.filter fun r => f r = .hyper).card * rowWeight = 129 :=
  frame_ledgers f hw fun r h => (weak_covers_iff r).1 (hcap r h)

/-- **Weak's own events never reach a wire.** A wire cell is displaced from the node along a root,
which has two nonzero coordinates, so at least one spatial. -/
theorem weak_misses_wires (r : Fin 4 → ℤ) (hr : ∃ i j, i ≠ j ∧ r i ≠ 0 ∧ r j ≠ 0) (t : ℕ)
    (L : List (Fin 4 → ℤ)) (hL : ∀ d ∈ L, d = 0) : (t : ℤ) • e 0 + L.sum ≠ r := by
  rw [internal_stays L hL t]
  obtain ⟨i, j, hij, hi, hj⟩ := hr
  intro h
  by_cases hi0 : i = 0
  · have hj0 : j ≠ 0 := fun h' => hij (hi0.trans h'.symm)
    apply hj
    rw [← h]
    simp [e, hj0]
  · apply hi
    rw [← h]
    simp [e, hi0]

end PMConstants.WeakLocality
