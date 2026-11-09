import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# The contour representation: cohomology core

A history of PM's spacetime model is a configuration `σ : X → Bool` on a connected graph `Γ`
(sites of spacetime), and its cost is its set of boundary edges, the **cut**
`{s(u,v) | Γ.Adj u v, σ u ≠ σ v}`. To rewrite the partition function as a polymer gas of contours,
two facts are needed. This file proves them.

* `hits C p`: the number of edges of the walk `p` lying in the edge set `C`.
* `cut_parity`: along any walk from `a` to `b`, a cut is crossed an odd number of times iff
  `σ a ≠ σ b`. Hence `cut_even`: **every cut meets every closed walk evenly.**
* `exists_potential`: conversely, on a connected graph, **every edge set that meets every closed
  walk evenly is the cut of a configuration**, which can be taken to be the vacuum (`false`) at a
  chosen root. `potential_unique`: that configuration is unique.

So cuts are exactly the even edge sets, and vacuum-rooted histories correspond one-to-one to
them.

**Contours.** Fix a family of plaquettes: short closed walks with no repeated edge. Two edges are
plaquette-adjacent when some plaquette contains both. The geometric premise `PlaquettesGenerate`
says that plaquettes generate the cycle space: an edge set meeting every plaquette evenly meets
every closed walk evenly. This holds for the hypercubic box (unit squares), and for `G □ path`
when it holds for the spatial graph `G`.

* `closed_piece_is_cut`: any part `γ` of a cut that is **closed under plaquette adjacency within
  the cut** is itself the cut of a vacuum-rooted configuration. In particular each
  plaquette-connected component of a boundary is a contour that can be added or removed on its own.

This replaces the much harder "boundaries of connected sets are connected" route. Contours are
connected sets in the plaquette-adjacency graph of edges, so `ContourCount` counts them directly
and their activity is exactly `q^|γ|`.
-/

namespace PMAction.MassGap.ContourRepresentation
open SimpleGraph

variable {X : Type*} [DecidableEq X] {Γ : SimpleGraph X}

/-- The number of edges of a walk that lie in `C`. -/
def hits (C : Finset (Sym2 X)) {a b : X} (p : Γ.Walk a b) : ℕ :=
  p.edges.countP fun e => decide (e ∈ C)

lemma hits_nil (C : Finset (Sym2 X)) (a : X) : hits C (Walk.nil : Γ.Walk a a) = 0 := by
  simp [hits]

lemma hits_cons (C : Finset (Sym2 X)) {a b c : X} (h : Γ.Adj a b) (p : Γ.Walk b c) :
    hits C (Walk.cons h p) = hits C p + if s(a, b) ∈ C then 1 else 0 := by
  simp [hits, Walk.edges_cons, List.countP_cons]

lemma hits_append (C : Finset (Sym2 X)) {a b c : X} (p : Γ.Walk a b) (q : Γ.Walk b c) :
    hits C (p.append q) = hits C p + hits C q := by
  simp [hits, Walk.edges_append, List.countP_append]

lemma hits_reverse (C : Finset (Sym2 X)) {a b : X} (p : Γ.Walk a b) :
    hits C p.reverse = hits C p := by
  simp [hits, Walk.edges_reverse, List.countP_reverse]

/-- `C` meets every closed walk an even number of times. -/
def EvenCycles (Γ : SimpleGraph X) (C : Finset (Sym2 X)) : Prop :=
  ∀ v (p : Γ.Walk v v), Even (hits C p)

/-- `C` is the cut of `σ`: an edge is in `C` iff its endpoints differ. -/
def IsCut (Γ : SimpleGraph X) (σ : X → Bool) (C : Finset (Sym2 X)) : Prop :=
  ∀ u v, Γ.Adj u v → (s(u, v) ∈ C ↔ σ u ≠ σ v)

/-- **Parity along a walk.** A cut is crossed an odd number of times iff the endpoints differ. -/
theorem cut_parity {σ : X → Bool} {C : Finset (Sym2 X)} (hC : IsCut Γ σ C) :
    ∀ {a b : X} (p : Γ.Walk a b), (Odd (hits C p) ↔ σ a ≠ σ b) := by
  intro a b p
  induction p with
  | nil => simp [hits_nil]
  | @cons a b c h p ih =>
    rw [hits_cons]
    have hab := hC a b h
    by_cases he : s(a, b) ∈ C
    · have hne : σ a ≠ σ b := hab.mp he
      simp only [he, ↓reduceIte]
      rw [Nat.odd_add_one, ih]
      cases ha : σ a <;> cases hb : σ b <;> cases hc : σ c <;> simp_all
    · have heq : σ a = σ b := by by_contra hne; exact he (hab.mpr hne)
      simp only [he, ↓reduceIte, add_zero]
      rw [ih, heq]

/-- **Every cut meets every closed walk evenly.** -/
theorem cut_even {σ : X → Bool} {C : Finset (Sym2 X)} (hC : IsCut Γ σ C) : EvenCycles Γ C := by
  intro v p
  have h := cut_parity hC p
  rw [← Nat.not_odd_iff_even, h]
  simp

/-- **Every even edge set is a cut**, of a configuration that is the vacuum at the root. -/
theorem exists_potential (hconn : Γ.Connected) (r : X) (C : Finset (Sym2 X))
    (hC : EvenCycles Γ C) : ∃ σ : X → Bool, σ r = false ∧ IsCut Γ σ C := by
  classical
  let w : ∀ v, Γ.Walk r v := fun v => (hconn.preconnected r v).some
  let σ : X → Bool := fun v => decide (Odd (hits C (w v)))
  -- the parity of any walk from the root is the parity of the chosen walk
  have hind : ∀ v (p : Γ.Walk r v), (Odd (hits C p) ↔ Odd (hits C (w v))) := by
    intro v p
    have he := hC r (p.append (w v).reverse)
    rw [hits_append, hits_reverse, Nat.even_add] at he
    rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, he]
  refine ⟨σ, ?_, ?_⟩
  · have he := hC r (w r)
    simp only [σ, decide_eq_false_iff_not, Nat.not_odd_iff_even]
    exact he
  · intro u v huv
    have hv := hind v ((w u).concat huv)
    have hcat : hits C ((w u).concat huv) = hits C (w u) + if s(u, v) ∈ C then 1 else 0 := by
      simp [hits, Walk.edges_concat, List.countP_append]
    rw [hcat] at hv
    simp only [σ, ne_eq, decide_eq_decide]
    by_cases he : s(u, v) ∈ C
    · simp only [he, ↓reduceIte] at hv
      rw [Nat.odd_add_one] at hv
      simp only [he, true_iff]
      intro h; rw [← hv] at h; exact absurd h (by tauto)
    · simp only [he, ↓reduceIte, add_zero] at hv
      simp only [he, false_iff, not_not]
      exact hv

/-- **Uniqueness.** On a connected graph, two configurations with the same cut that agree at one
site agree everywhere. -/
theorem potential_unique (hconn : Γ.Connected) {σ τ : X → Bool} {C : Finset (Sym2 X)}
    (hσ : IsCut Γ σ C) (hτ : IsCut Γ τ C) (r : X) (hr : σ r = τ r) : σ = τ := by
  funext v
  obtain ⟨p⟩ := hconn.preconnected r v
  have h1 := cut_parity hσ p
  have h2 := cut_parity hτ p
  have : (σ r ≠ σ v ↔ τ r ≠ τ v) := h1.symm.trans h2
  rw [hr] at this
  cases hv1 : σ v <;> cases hv2 : τ v <;> cases hrr : τ r <;> simp_all

/-! ### Contours: plaquette-closed pieces of a cut -/

/-- Plaquettes: closed walks without repeated edges, given by their edge sets. -/
def IsPlaquette (Γ : SimpleGraph X) (P : Finset (Sym2 X)) : Prop :=
  ∃ v, ∃ p : Γ.Walk v v, p.edges.Nodup ∧ p.edges.toFinset = P

/-- **Geometric premise.** Plaquettes generate the cycle space. -/
def PlaquettesGenerate (Γ : SimpleGraph X) (plaq : Finset (Finset (Sym2 X))) : Prop :=
  ∀ C : Finset (Sym2 X), (∀ P ∈ plaq, Even (P ∩ C).card) → EvenCycles Γ C

/-- On a plaquette, the number of cut edges is the walk's hit count. -/
lemma card_inter_eq_hits {P C : Finset (Sym2 X)} {v : X} (p : Γ.Walk v v) (hnd : p.edges.Nodup)
    (hP : p.edges.toFinset = P) : (P ∩ C).card = hits C p := by
  classical
  rw [← hP, hits, List.countP_eq_length_filter]
  have : p.edges.toFinset ∩ C = (p.edges.filter fun e => decide (e ∈ C)).toFinset := by
    ext e; simp
  rw [this, List.toFinset_card_of_nodup (hnd.filter _)]

/-- A cut meets every plaquette evenly. -/
lemma cut_even_plaquette {σ : X → Bool} {C : Finset (Sym2 X)} (hC : IsCut Γ σ C)
    {P : Finset (Sym2 X)} (hP : IsPlaquette Γ P) : Even (P ∩ C).card := by
  obtain ⟨v, p, hnd, hPe⟩ := hP
  rw [card_inter_eq_hits p hnd hPe]
  exact cut_even hC v p

/-- **Plaquette-closed pieces of a cut are cuts.** If `γ ⊆ C = cut σ` and `γ` is closed under
plaquette adjacency within `C`, then `γ` is the cut of a vacuum-rooted configuration. -/
theorem closed_piece_is_cut (hconn : Γ.Connected) (r : X) (plaq : Finset (Finset (Sym2 X)))
    (hplaq : ∀ P ∈ plaq, IsPlaquette Γ P) (hgen : PlaquettesGenerate Γ plaq)
    {σ : X → Bool} {C γ : Finset (Sym2 X)} (hC : IsCut Γ σ C) (hγC : γ ⊆ C)
    (hclosed : ∀ e ∈ γ, ∀ e' ∈ C, (∃ P ∈ plaq, e ∈ P ∧ e' ∈ P) → e' ∈ γ) :
    ∃ τ : X → Bool, τ r = false ∧ IsCut Γ τ γ := by
  apply exists_potential hconn r γ
  apply hgen
  intro P hP
  by_cases hne : (P ∩ γ).Nonempty
  · obtain ⟨e, he⟩ := hne
    rw [Finset.mem_inter] at he
    have heq : P ∩ γ = P ∩ C := by
      ext e'
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hγC h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hclosed e he.2 e' h2 ⟨P, hP, he.1, h1⟩⟩
    rw [heq]
    exact cut_even_plaquette hC (hplaq P hP)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact ⟨0, rfl⟩

end PMAction.MassGap.ContourRepresentation
