import PMAction.MassGap.SlabGap

/-!
# The gap on a cubic box

The abstract spatial lattice of `SlabGap` is instantiated by the `d`-dimensional box with side
`n + 1`: a point thickened `d` times by `G ↦ G □ [0, n]`. Each thickening carries the plaquette
data along (`slab_generate`, `slabPlaq_isPlaquette`) and the local bounds
(`SlabDegree.card_slabPlaq_le`, `spatial_through`, `squares_through`):
plaquettes have `≤ 4` edges, at most `8 d²` pass through an edge, and the degree is `2d`.

`box_mass_gap`: on the slab over the `d`-box (spacetime of dimension `d + 1`; `d = 3` is
Euclidean 4D), if `β ≥ 2 log(16 (32 d² + 64 d + 1)²)`, every flip-even excited state of `T²` has
mass at least `β/2` per tick, uniformly in the side `n` (and in the slab length). For `d = 3` the
condition is `β ≥ 2 log(16 · 481²) ≈ 30.2`.
-/

namespace PMAction.MassGap.CubicBox
open Finset SimpleGraph ContourRepresentation ContourGas SlabGeometry SlabDegree Matrix

/-- A spatial lattice with plaquette data and local bounds. -/
structure Lat where
  V : Type
  [fin : Fintype V]
  [dec : DecidableEq V]
  G : SimpleGraph V
  [decAdj : DecidableRel G.Adj]
  plaq : Finset (Finset (Sym2 V))
  k : ℕ
  m : ℕ
  Δ : ℕ
  conn : G.Connected
  plaqE : ∀ P ∈ plaq, P ⊆ G.edgeFinset
  plaqP : ∀ P ∈ plaq, IsPlaquette G P
  gen : PlaquettesGenerate G plaq
  hk : ∀ P ∈ plaq, P.card ≤ k
  hm : ∀ e0, (plaq.filter (e0 ∈ ·)).card ≤ m
  hΔ : ∀ v, G.degree v ≤ Δ

attribute [instance] Lat.fin Lat.dec Lat.decAdj

lemma plaquette_sub {X : Type*} [Fintype X] [DecidableEq X] {Γ : SimpleGraph X} [DecidableRel Γ.Adj]
    {P : Finset (Sym2 X)} (hP : IsPlaquette Γ P) : P ⊆ Γ.edgeFinset := by
  obtain ⟨v, p, -, rfl⟩ := hP
  intro e he
  rw [List.mem_toFinset] at he
  rw [mem_edgeFinset]
  exact p.edges_subset_edgeSet he

open Classical in
lemma path_degree_le (n : ℕ) (i : Fin n) : (pathGraph n).degree i ≤ 2 := by
  rw [← card_neighborFinset_eq_degree]
  have := card_le_card_of_injOn (fun j : Fin n => j.val) (t := ({i.val - 1, i.val + 1} : Finset ℕ))
    (fun j hj => by
      have hj' : j ∈ (pathGraph n).neighborFinset i := hj
      rw [mem_neighborFinset, pathGraph_adj] at hj'
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega)
    (fun a _ b _ h => Fin.ext h)
  exact this.trans card_le_two

/-- The point. -/
noncomputable def point : Lat where
  V := Unit
  G := ⊥
  decAdj := Classical.decRel _
  plaq := ∅
  k := 0
  m := 0
  Δ := 0
  conn := { preconnected := fun u v => by rw [Subsingleton.elim u v], nonempty := ⟨()⟩ }
  plaqE := by simp
  plaqP := by simp
  gen := by
    intro C _ v p
    cases p with
    | nil => simp [hits_nil]
    | cons h _ => exact absurd h (by simp)
  hk := by simp
  hm := by simp
  hΔ := fun v => by simp

open Classical in
/-- Thicken by one direction of side `n + 1`. -/
noncomputable def extend (A : Lat) (n : ℕ) : Lat where
  V := A.V × Fin (n + 1)
  G := slab A.G n
  decAdj := Classical.decRel _
  plaq := slabPlaq A.G n A.plaq
  k := max A.k 4
  m := A.m + 8 * A.Δ
  Δ := A.Δ + 2
  conn := A.conn.boxProd (pathGraph_connected n)
  plaqE := fun P hP => plaquette_sub (slabPlaq_isPlaquette A.G n A.plaq A.plaqP P hP)
  plaqP := slabPlaq_isPlaquette A.G n A.plaq A.plaqP
  gen := slab_generate A.G n A.plaq A.conn A.conn.nonempty.some A.plaqE A.gen
  hk := card_slabPlaq_le A.G n A.plaq A.hk
  hm := fun e => by
    rw [slabPlaq, filter_union]
    exact (card_union_le _ _).trans
      (Nat.add_le_add (spatial_through n A.plaq e A.hm) (squares_through A.G n e A.hΔ))
  hΔ := fun x => by
    obtain ⟨v, t⟩ := x
    rw [← card_neighborFinset_eq_degree]
    have hsub : (slab A.G n).neighborFinset (v, t) ⊆
        (A.G.neighborFinset v ×ˢ {t}) ∪ ({v} ×ˢ (pathGraph (n + 1)).neighborFinset t) := by
      intro y hy
      obtain ⟨w, s⟩ := y
      rw [mem_neighborFinset, boxProd_adj] at hy
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        exact mem_union_left _ (mem_product.mpr ⟨(mem_neighborFinset _ _ _).mpr h1,
          by rw [mem_singleton]; exact h2.symm⟩)
      · simp only at h1 h2
        exact mem_union_right _ (mem_product.mpr ⟨by rw [mem_singleton]; exact h2.symm,
          (mem_neighborFinset _ _ _).mpr h1⟩)
    have key : ((slab A.G n).neighborFinset (v, t)).card ≤ A.Δ + 2 := by
      refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
      rw [card_product, card_product, card_singleton, card_singleton, mul_one, one_mul,
        card_neighborFinset_eq_degree, card_neighborFinset_eq_degree]
      have := A.hΔ v
      have := path_degree_le (n + 1) t
      omega
    convert key

/-- The `d`-dimensional box of side `n + 1`. -/
noncomputable def box (d n : ℕ) : Lat := (fun A => extend A n)^[d] point

lemma box_succ (d n : ℕ) : box (d + 1) n = extend (box d n) n :=
  Function.iterate_succ_apply' _ _ _

lemma box_bounds (n : ℕ) : ∀ d : ℕ,
    (box d n).k ≤ 4 ∧ (box d n).m ≤ 8 * d * d ∧ (box d n).Δ = 2 * d := by
  intro d
  induction d with
  | zero => exact ⟨by simp [box, point], by simp [box, point], by simp [box, point]⟩
  | succ d ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [box_succ]
    refine ⟨show max (box d n).k 4 ≤ 4 from max_le h1 le_rfl, ?_, ?_⟩
    · show (box d n).m + 8 * (box d n).Δ ≤ 8 * (d + 1) * (d + 1)
      rw [h3]; nlinarith
    · show (box d n).Δ + 2 = 2 * (d + 1)
      rw [h3]; ring

/-- **The mass gap on a cubic box.** -/
theorem box_mass_gap (d n : ℕ) {β : ℝ}
    (hβ : 2 * Real.log (16 * (((32 * d * d + 64 * d : ℕ) : ℝ) + 1) ^ 2) ≤ β) :
    ∃ Λ : ℝ, 0 < Λ ∧
      (∀ (ψ : ((box d n).V → Bool) → ℝ) (lam : ℝ), ψ ≠ 0 → SlabGap.Even' ψ →
        (TransferSlab.transfer (box d n).G (Real.exp (-β)) *
          TransferSlab.transfer (box d n).G (Real.exp (-β))) *ᵥ ψ = lam • ψ → 0 < lam →
        β / 2 ≤ Real.log (Λ / lam) / 2 ∨
          (lam = Λ ∧ ψ ⬝ᵥ TransferSlab.v₀ (box d n).G (Real.exp (-β)) ≠ 0)) := by
  obtain ⟨hk, hm, hΔ⟩ := box_bounds n d
  have hD : max 4 4 * (8 * d * d + 8 * (2 * d)) = 32 * d * d + 64 * d := by
    simp only [max_self]; ring
  have hβ' : 2 * Real.log (16 * (((max 4 4 * (8 * d * d + 8 * (2 * d)) : ℕ) : ℝ) + 1) ^ 2) ≤ β := by
    rw [hD]; exact hβ
  exact SlabGap.slab_mass_gap (box d n).conn (box d n).plaqE (box d n).plaqP (box d n).gen
    (fun P hP => ((box d n).hk P hP).trans hk) (fun e => ((box d n).hm e).trans hm)
    (fun v => ((box d n).hΔ v).trans hΔ.le) hβ'

end PMAction.MassGap.CubicBox
