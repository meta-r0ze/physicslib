import PMAction.MassGap.ContourRepresentation
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The spacetime slab: plaquettes generate the cycle space

The slab of `L + 1` ticks over a spatial graph `G` is `G □ path(L+1)`: neighbours in space at one
tick, or one site at consecutive ticks (`SpacetimeCost`). Its plaquettes are

* the plaquettes of `G` copied into every slice (`spatialPlaq`), and
* the unit squares between two neighbouring sites and two consecutive ticks (`squares`).

* `slab_generate`: **if the plaquettes of `G` generate its cycle space, the slab plaquettes
  generate the slab's cycle space.** This is the geometric premise of `ContourGas` for the PM
  slab, reduced to the same premise for the spatial graph alone. Proof: an edge set even on all
  plaquettes restricts to an even set in slice `0`, which has a potential; that potential is
  carried up through time by flipping across every temporal edge in the set, and the squares make
  every spatial edge at the next tick consistent.
* `square_isPlaquette`, `spatial_isPlaquette`: the slab plaquettes are closed walks without
  repeated edges.

Time here is a path (open ends), so there is no winding cycle.
-/

namespace PMAction.MassGap.SlabGeometry
open Finset SimpleGraph ContourRepresentation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (L : ℕ)

/-- The slab graph. -/
abbrev slab : SimpleGraph (V × Fin (L + 1)) := G □ pathGraph (L + 1)

/-- The temporal edge at site `v` from tick `s` to `s + 1`. -/
def tE (v : V) (s : Fin L) : Sym2 (V × Fin (L + 1)) := s((v, s.castSucc), (v, s.succ))

/-- The unit square between neighbours `u`, `v` and ticks `s`, `s + 1`. -/
def square (u v : V) (s : Fin L) : Finset (Sym2 (V × Fin (L + 1))) :=
  {s((u, s.castSucc), (v, s.castSucc)), s((u, s.succ), (v, s.succ)), tE L u s, tE L v s}

/-- All unit squares. -/
def squares : Finset (Finset (Sym2 (V × Fin (L + 1)))) :=
  (((univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2) ×ˢ (univ : Finset (Fin L))).image
    fun p => square L p.1.1 p.1.2 p.2

/-- Spatial plaquettes copied into every slice. -/
def spatialPlaq (plaqG : Finset (Finset (Sym2 V))) : Finset (Finset (Sym2 (V × Fin (L + 1)))) :=
  (plaqG ×ˢ (univ : Finset (Fin (L + 1)))).image
    fun p => p.1.image (Sym2.map fun v => (v, p.2))

/-- The slab plaquettes. -/
def slabPlaq (plaqG : Finset (Finset (Sym2 V))) : Finset (Finset (Sym2 (V × Fin (L + 1)))) :=
  spatialPlaq L plaqG ∪ squares G L

/-- Parity of four distinct edges on an even square. -/
lemma four_parity {α : Type*} [DecidableEq α] {a b c d : α} (C : Finset α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : Even (({a, b, c, d} : Finset α) ∩ C).card) :
    decide (b ∈ C) = ((decide (a ∈ C) ^^ decide (c ∈ C)) ^^ decide (d ∈ C)) := by
  have hcard : (({a, b, c, d} : Finset α) ∩ C).card =
      (if a ∈ C then 1 else 0) + ((if b ∈ C then 1 else 0) + ((if c ∈ C then 1 else 0) +
        (if d ∈ C then 1 else 0))) := by
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter, sum_insert (by simp [hab, hac, had]),
      sum_insert (by simp [hbc, hbd]), sum_insert (by simp [hcd]), sum_singleton]
  rw [hcard] at h
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> by_cases hc : c ∈ C <;> by_cases hd : d ∈ C <;>
    simp only [ha, hb, hc, hd, ↓reduceIte, decide_true, decide_false] at h ⊢ <;> revert h <;>
    decide

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma tE_ne {v : V} {s : Fin L} : (v, s.castSucc) ≠ (v, s.succ) := by
  intro h
  have := congrArg (fun p => (p.2 : Fin (L + 1)).val) h
  simp at this

set_option linter.unusedSimpArgs false in
/-- **Plaquettes generate the slab's cycle space.** -/
theorem slab_generate (plaqG : Finset (Finset (Sym2 V))) (hconnG : G.Connected) (b : V)
    (hplaqG : ∀ P ∈ plaqG, P ⊆ G.edgeFinset) (hG : PlaquettesGenerate G plaqG) :
    PlaquettesGenerate (slab G L) (slabPlaq G L plaqG) := by
  classical
  intro C hC
  -- slice 0
  let lift0 : Sym2 V → Sym2 (V × Fin (L + 1)) := Sym2.map fun v => (v, (0 : Fin (L + 1)))
  have hlift_inj : Function.Injective lift0 :=
    Sym2.map.injective (fun x y h => (Prod.ext_iff.mp h).1)
  let C0 : Finset (Sym2 V) := G.edgeFinset.filter fun e => lift0 e ∈ C
  have hC0 : EvenCycles G C0 := by
    apply hG
    intro P hP
    have hsp : P.image lift0 ∈ slabPlaq G L plaqG := by
      apply mem_union_left
      exact mem_image.mpr ⟨(P, 0), mem_product.mpr ⟨hP, mem_univ _⟩, rfl⟩
    have he := hC _ hsp
    have e : (P.image lift0 ∩ C).card = (P ∩ C0).card := by
      have : P.image lift0 ∩ C = (P ∩ C0).image lift0 := by
        ext y
        simp only [mem_inter, mem_image, C0, mem_filter]
        constructor
        · rintro ⟨⟨e, he, rfl⟩, hy⟩; exact ⟨e, ⟨he, hplaqG P hP he, hy⟩, rfl⟩
        · rintro ⟨e, ⟨he, -, hy⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hy⟩
      rw [this, card_image_of_injective _ hlift_inj]
    rwa [e] at he
  obtain ⟨σ0, -, hσ0⟩ := exists_potential hconnG b C0 hC0
  -- carry the potential through time
  let tm : V → ℕ → Bool := fun v s => if h : s < L then decide (tE L v ⟨s, h⟩ ∈ C) else false
  let τ : V → ℕ → Bool := fun v => Nat.rec (σ0 v) (fun s acc => acc ^^ tm v s)
  have hτ0 : ∀ v, τ v 0 = σ0 v := fun v => rfl
  have hτs : ∀ v s, τ v (s + 1) = (τ v s ^^ tm v s) := fun v s => rfl
  let σ : V × Fin (L + 1) → Bool := fun p => τ p.1 p.2.val
  -- spatial edges at every tick
  have hspat : ∀ s (hs : s < L + 1) u v, G.Adj u v →
      (s((u, (⟨s, hs⟩ : Fin (L + 1))), (v, ⟨s, hs⟩)) ∈ C ↔ τ u s ≠ τ v s) := by
    intro s
    induction s with
    | zero =>
      intro hs u v huv
      have := hσ0 u v huv
      have e0 : s((u, (⟨0, hs⟩ : Fin (L + 1))), (v, ⟨0, hs⟩)) = lift0 s(u, v) := rfl
      rw [e0, hτ0, hτ0, ← this]
      simp only [C0, mem_filter, mem_edgeFinset, mem_edgeSet, huv, true_and]
    | succ s ih =>
      intro hs u v huv
      have hsL : s < L := by omega
      have ih' := ih (by omega) u v huv
      let sf : Fin L := ⟨s, hsL⟩
      have hsq : square L u v sf ∈ slabPlaq G L plaqG := by
        apply mem_union_right
        exact mem_image.mpr ⟨((u, v), sf), mem_product.mpr ⟨by simp [huv], mem_univ _⟩, rfl⟩
      have hne : u ≠ v := G.ne_of_adj huv
      have hpar := four_parity C (a := s((u, sf.castSucc), (v, sf.castSucc)))
        (b := s((u, sf.succ), (v, sf.succ))) (c := tE L u sf) (d := tE L v sf)
        (by simp [Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, sf])
        (by simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, sf, hne])
        (by simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, sf, hne])
        (by simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, sf, hne])
        (by simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, sf, hne])
        (by simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff, sf, hne])
        (hC _ hsq)
      have ecs : (sf.castSucc : Fin (L + 1)) = ⟨s, by omega⟩ := Fin.ext rfl
      have esu : (sf.succ : Fin (L + 1)) = ⟨s + 1, hs⟩ := Fin.ext rfl
      rw [ecs, esu] at hpar
      have htu : tm u s = decide (tE L u sf ∈ C) := by simp [tm, hsL, sf]
      have htv : tm v s = decide (tE L v sf ∈ C) := by simp [tm, hsL, sf]
      rw [hτs, hτs, htu, htv]
      set X := s((u, (⟨s + 1, hs⟩ : Fin (L + 1))), (v, ⟨s + 1, hs⟩))
      set Y := s((u, (⟨s, by omega⟩ : Fin (L + 1))), (v, ⟨s, by omega⟩))
      have hX : (X ∈ C) ↔ decide (X ∈ C) = true := decide_eq_true_iff.symm
      have hY : decide (Y ∈ C) = (τ u s != τ v s) := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, ih']; simp
      rw [hX, hpar, hY]
      cases τ u s <;> cases τ v s <;> cases decide (tE L u sf ∈ C) <;>
        cases decide (tE L v sf ∈ C) <;> decide
  -- the potential's cut is `C`
  have hcut : IsCut (slab G L) σ C := by
    intro x y hxy
    rw [boxProd_adj] at hxy
    rcases hxy with ⟨huv, ht⟩ | ⟨hst, hxy1⟩
    · obtain ⟨u, t⟩ := x; obtain ⟨v, t'⟩ := y
      simp only at huv ht; subst ht
      exact hspat t.val t.isLt u v huv
    · obtain ⟨u, t⟩ := x; obtain ⟨v, t'⟩ := y
      simp only at hst hxy1; subst hxy1
      rw [pathGraph_adj] at hst
      rcases hst with h | h
      · have hsL : t.val < L := by have := t'.isLt; omega
        have e : s((u, t), (u, t')) = tE L u ⟨t.val, hsL⟩ := by
          simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]; omega
        have hσ : σ (u, t') = (σ (u, t) ^^ tm u t.val) := by
          show τ u t'.val = _; rw [← h, hτs]
        rw [hσ, e]
        simp only [tm, hsL, ↓reduceDIte]
        by_cases hm : tE L u ⟨t.val, hsL⟩ ∈ C <;> cases σ (u, t) <;> simp [hm]
      · have hsL : t'.val < L := by have := t.isLt; omega
        have e : s((u, t), (u, t')) = tE L u ⟨t'.val, hsL⟩ := by
          simp [tE, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]; omega
        have hσ : σ (u, t) = (σ (u, t') ^^ tm u t'.val) := by
          show τ u t.val = _; rw [← h, hτs]
        rw [hσ, e]
        simp only [tm, hsL, ↓reduceDIte]
        by_cases hm : tE L u ⟨t'.val, hsL⟩ ∈ C <;> cases σ (u, t') <;> simp [hm]
  exact cut_even hcut


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma slab_adj_time (u : V) (s : Fin L) :
    (slab G L).Adj (u, s.castSucc) (u, s.succ) := by
  rw [boxProd_adj]; right
  refine ⟨?_, rfl⟩
  rw [pathGraph_adj]; left; simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma slab_adj_space {u v : V} (h : G.Adj u v) (t : Fin (L + 1)) :
    (slab G L).Adj (u, t) (v, t) := by
  rw [boxProd_adj]; left; exact ⟨h, rfl⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Unit squares are plaquettes. -/
theorem square_isPlaquette {u v : V} (h : G.Adj u v) (s : Fin L) :
    IsPlaquette (slab G L) (square L u v s) := by
  have hne : u ≠ v := G.ne_of_adj h
  have hts : s.castSucc ≠ s.succ := Fin.castSucc_lt_succ.ne
  let p : (slab G L).Walk (u, s.castSucc) (u, s.castSucc) :=
    Walk.cons (slab_adj_space G L h s.castSucc)
      (Walk.cons ((slab_adj_time G L v s))
        (Walk.cons ((slab_adj_space G L h s.succ).symm)
          (Walk.cons ((slab_adj_time G L u s).symm) Walk.nil)))
  refine ⟨_, p, ?_, ?_⟩
  · simp [p, Walk.edges_cons, Prod.ext_iff, hne, hne.symm, hts, hts.symm]
  · ext e
    simp only [p, Walk.edges_cons, Walk.edges_nil, List.toFinset_cons, List.toFinset_nil,
      square, tE, mem_insert, mem_singleton, insert_empty_eq]
    constructor
    · rintro (h1 | h1 | h1 | h1) <;> subst h1 <;> simp [Sym2.eq_swap]
    · rintro (h1 | h1 | h1 | h1) <;> subst h1 <;> simp [Sym2.eq_swap]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Spatial plaquettes copied into a slice are plaquettes. -/
theorem spatial_isPlaquette {P : Finset (Sym2 V)} (hP : IsPlaquette G P) (t : Fin (L + 1)) :
    IsPlaquette (slab G L) (P.image (Sym2.map fun v => (v, t))) := by
  obtain ⟨v, p, hnd, hPe⟩ := hP
  let f := (G.boxProdLeft (pathGraph (L + 1)) t).toHom
  have hinj : Function.Injective (Sym2.map f) :=
    Sym2.map.injective fun a b h => (Prod.ext_iff.mp h).1
  refine ⟨f v, p.map f, ?_, ?_⟩
  · rw [Walk.edges_map]
    exact hnd.map hinj
  · rw [Walk.edges_map, ← hPe]
    ext e
    simp only [List.mem_toFinset, List.mem_map, mem_image]
    rfl

/-- All slab plaquettes are plaquettes. -/
theorem slabPlaq_isPlaquette (plaqG : Finset (Finset (Sym2 V)))
    (hplaqG : ∀ P ∈ plaqG, IsPlaquette G P) :
    ∀ P ∈ slabPlaq G L plaqG, IsPlaquette (slab G L) P := by
  intro P hP
  rcases mem_union.mp hP with h | h
  · obtain ⟨⟨Q, t⟩, hQ, rfl⟩ := mem_image.mp h
    exact spatial_isPlaquette G L (hplaqG Q (mem_product.mp hQ).1) t
  · obtain ⟨⟨⟨u, v⟩, s⟩, hq, rfl⟩ := mem_image.mp h
    have huv : G.Adj u v := by simpa using (mem_product.mp hq).1
    exact square_isPlaquette G L huv s

end PMAction.MassGap.SlabGeometry
