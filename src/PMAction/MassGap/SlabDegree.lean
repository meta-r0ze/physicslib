import PMAction.MassGap.SlabGeometry
import PMAction.MassGap.ContourGas

/-!
# The slab plaquette graph has bounded degree, uniformly in the slab length

`SlabClustering` and `SlabGap` need the plaquette graph of the slab `G □ [0, L]` to have degree
`≤ D` for every `L`. This file gives an explicit `D` that depends only on the spatial lattice:

* every plaquette of the slab has at most `max k 4` edges (`k` bounds the spatial plaquettes; unit
  squares have four);
* every slab edge lies in at most `m + 8Δ` plaquettes (`m` bounds the spatial plaquettes through
  one spatial edge, `Δ` bounds the degree of `G`): the spatial copies come from one slice, and
  a unit square through an edge has a corner at an endpoint of that edge and a tick next to it.

So `slab_degree_le`: `degree ≤ max k 4 · (m + 8Δ)`.
-/

namespace PMAction.MassGap.SlabDegree
open Finset SimpleGraph ContourRepresentation ContourGas SlabGeometry
open Classical

/-- Degree in the plaquette graph is at most the total size of the plaquettes through an edge. -/
theorem degree_le_sum {X : Type*} [Fintype X] [DecidableEq X]
    (plaq : Finset (Finset (Sym2 X))) (e : Sym2 X) :
    (plaqGraph plaq).degree e ≤ ∑ P ∈ plaq.filter (e ∈ ·), P.card := by
  rw [← card_neighborFinset_eq_degree]
  refine (card_le_card ?_).trans card_biUnion_le
  intro e' he'
  rw [mem_neighborFinset] at he'
  obtain ⟨-, P, hP, h1, h2⟩ := he'
  exact mem_biUnion.mpr ⟨P, mem_filter.mpr ⟨hP, h1⟩, h2⟩

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (L : ℕ)
  (plaqG : Finset (Finset (Sym2 V)))

omit [Fintype V] in
lemma card_square_le (u v : V) (s : Fin L) : (square L u v s).card ≤ 4 := by
  unfold square
  refine (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
    (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))

lemma card_slabPlaq_le {k : ℕ} (hk : ∀ P ∈ plaqG, P.card ≤ k) :
    ∀ P ∈ slabPlaq G L plaqG, P.card ≤ max k 4 := by
  intro P hP
  rcases mem_union.mp hP with h | h
  · rw [spatialPlaq, mem_image] at h
    obtain ⟨⟨P0, t⟩, hP0, rfl⟩ := h
    exact card_image_le.trans ((hk P0 (mem_product.mp hP0).1).trans (le_max_left _ _))
  · rw [squares, mem_image] at h
    obtain ⟨⟨⟨u, v⟩, s⟩, -, rfl⟩ := h
    exact (card_square_le L u v s).trans (le_max_right _ _)

omit [Fintype V] in
lemma spatial_through (e : Sym2 (V × Fin (L + 1))) {m : ℕ}
    (hm : ∀ e0, (plaqG.filter (e0 ∈ ·)).card ≤ m) :
    ((spatialPlaq L plaqG).filter (e ∈ ·)).card ≤ m := by
  induction e using Sym2.ind with
  | h x y =>
    rw [spatialPlaq, filter_image]
    refine card_image_le.trans ?_
    have hsub : (plaqG ×ˢ (univ : Finset (Fin (L + 1)))).filter
        (fun p => s(x, y) ∈ p.1.image (Sym2.map fun v => (v, p.2))) ⊆
        (plaqG.filter (s(x.1, y.1) ∈ ·)) ×ˢ {x.2} := by
      intro p hp
      rw [mem_filter, mem_product] at hp
      obtain ⟨⟨hP, -⟩, he⟩ := hp
      rw [mem_image] at he
      obtain ⟨e0, he0, hmap⟩ := he
      induction e0 using Sym2.ind with
      | h u w =>
        rw [Sym2.map_mk, Sym2.eq_iff] at hmap
        rw [mem_product, mem_filter, mem_singleton]
        rcases hmap with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2; exact ⟨⟨hP, he0⟩, rfl⟩
        · subst h1; subst h2; exact ⟨⟨hP, by rw [Sym2.eq_swap]; exact he0⟩, rfl⟩
    refine (card_le_card hsub).trans ?_
    rw [card_product, card_singleton, mul_one]
    exact hm _

lemma squares_through (e : Sym2 (V × Fin (L + 1))) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ((squares G L).filter (e ∈ ·)).card ≤ 8 * Δ := by
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    rw [squares, filter_image]
    refine card_image_le.trans ?_
    set A : Finset V := {x1, y1}
    set pairs := (univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2 ∧ (p.1 ∈ A ∨ p.2 ∈ A)
    set S := (univ : Finset (Fin L)).filter fun s => s.val = x2.val ∨ s.val + 1 = x2.val
    have hsub : (((univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2) ×ˢ
        (univ : Finset (Fin L))).filter
          (fun p => s((x1, x2), (y1, y2)) ∈ square L p.1.1 p.1.2 p.2) ⊆ pairs ×ˢ S := by
      intro p hp
      obtain ⟨⟨u, v⟩, s⟩ := p
      simp only [mem_filter, mem_product, mem_univ, true_and] at hp
      obtain ⟨⟨hadj, -⟩, hsq⟩ := hp
      simp only [mem_product, mem_filter, mem_univ, true_and, pairs, S, A, mem_insert,
        mem_singleton]
      refine ⟨⟨hadj, ?_⟩, ?_⟩ <;>
      · simp only [square, tE, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hsq
        rcases hsq with (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) |
          (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) |
          (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) |
          (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) <;>
        subst_vars <;> simp [Fin.val_succ]
    refine (card_le_card hsub).trans ?_
    rw [card_product]
    -- adjacent pairs touching `A`
    have hpairs : pairs.card ≤ 4 * Δ := by
      have hsub2 : pairs ⊆ A.biUnion fun a =>
          ({a} ×ˢ G.neighborFinset a) ∪ (G.neighborFinset a ×ˢ {a}) := by
        intro p hp
        obtain ⟨u, v⟩ := p
        simp only [pairs, mem_filter, mem_univ, true_and] at hp
        obtain ⟨hadj, hA⟩ := hp
        rw [mem_biUnion]
        rcases hA with hu | hv
        · exact ⟨u, hu, mem_union_left _ (mem_product.mpr ⟨mem_singleton_self _,
            (mem_neighborFinset _ _ _).mpr hadj⟩)⟩
        · exact ⟨v, hv, mem_union_right _ (mem_product.mpr
            ⟨(mem_neighborFinset _ _ _).mpr hadj.symm, mem_singleton_self _⟩)⟩
      refine (card_le_card hsub2).trans (card_biUnion_le.trans ?_)
      have hA2 : A.card ≤ 2 := card_le_two
      have hterm : ∀ a ∈ A, (({a} ×ˢ G.neighborFinset a) ∪
          (G.neighborFinset a ×ˢ {a})).card ≤ 2 * Δ := by
        intro a _
        refine (card_union_le _ _).trans ?_
        rw [card_product, card_product, card_singleton, one_mul, mul_one,
          card_neighborFinset_eq_degree]
        have := hΔ a; omega
      refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [smul_eq_mul]
      nlinarith
    have hS : S.card ≤ 2 := by
      have := card_le_card_of_injOn (fun s : Fin L => s.val) (t := ({x2.val, x2.val - 1} : Finset ℕ))
        (fun s hs => by
          have h : s ∈ S := hs
          simp only [S, mem_filter, mem_univ, true_and] at h
          simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
          omega)
        (fun a _ b _ h => Fin.ext h)
      exact this.trans card_le_two
    calc pairs.card * S.card ≤ (4 * Δ) * 2 := Nat.mul_le_mul hpairs hS
      _ = 8 * Δ := by ring

/-- **The slab plaquette degree is bounded, uniformly in `L`.** -/
theorem slab_degree_le {k m Δ : ℕ} (hk : ∀ P ∈ plaqG, P.card ≤ k)
    (hm : ∀ e0, (plaqG.filter (e0 ∈ ·)).card ≤ m) (hΔ : ∀ v, G.degree v ≤ Δ)
    (e : Sym2 (V × Fin (L + 1))) :
    (plaqGraph (slabPlaq G L plaqG)).degree e ≤ max k 4 * (m + 8 * Δ) := by
  refine (degree_le_sum _ e).trans ?_
  refine (sum_le_card_nsmul _ _ _ fun P hP =>
    card_slabPlaq_le G L plaqG hk P (mem_filter.mp hP).1).trans ?_
  rw [smul_eq_mul, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  rw [slabPlaq, filter_union]
  exact (card_union_le _ _).trans
    (Nat.add_le_add (spatial_through L plaqG e hm) (squares_through G L e hΔ))

end PMAction.MassGap.SlabDegree
