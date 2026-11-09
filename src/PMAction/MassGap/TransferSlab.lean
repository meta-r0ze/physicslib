import PMAction.MassGap.SlabGeometry
import PMAction.MassGap.HistorySum
import PMAction.MassGap.TransferHistory
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The slab sum is a transfer-matrix product

A slab configuration `σ : V × Fin (L+1) → Bool` is a history of slices
`h t = σ(·, t) : V → Bool`. Its boundary splits into spatial boundary edges inside each
slice and temporal flips between consecutive slices:

* `cut_decomp`: `|∂σ| = Σ_t |∂_G (h t)| + Σ_s ham(h s, h (s+1))`.
* `slab_transfer`: with `T(s, s') = r^{c s} q^{ham(s,s')} r^{c s'}`, `r² = q`, and
  `v₀ s = r^{c s}` (`c s = |∂_G s|`),
  `Σ_σ f(σ_0) g(σ_L) q^{|∂σ|} = (v₀ f) ⬝ Tᴸ (v₀ g)`.

So the PM slab history sum is a transfer-matrix product.
-/

namespace PMAction.MassGap.TransferSlab
open Finset SimpleGraph ContourRepresentation HistorySum SlabGeometry
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
lemma mem_cutSet_iff {X : Type*} [Fintype X] (Γ : SimpleGraph X) [DecidableRel Γ.Adj]
    (σ : X → Bool) (x y : X) : s(x, y) ∈ cutSet Γ σ ↔ Γ.Adj x y ∧ σ x ≠ σ y := by
  simp [cutSet]

/-- The slice of a slab configuration at tick `t`. -/
def slice {L : ℕ} (σ : V × Fin (L + 1) → Bool) (t : Fin (L + 1)) : V → Bool := fun v => σ (v, t)

/-- Spatial boundary size of a slice state. -/
def cost (s : V → Bool) : ℕ := (cutSet G s).card

/-- Number of sites that flip between two slice states. -/
def ham (s s' : V → Bool) : ℕ := (univ.filter fun v => s v ≠ s' v).card

variable (L : ℕ)

/-- Spatial boundary edges of the slab, by slice. -/
def spatialCut (σ : V × Fin (L + 1) → Bool) : Finset (Sym2 (V × Fin (L + 1))) :=
  univ.biUnion fun t : Fin (L + 1) => (cutSet G (slice σ t)).image (Sym2.map fun v => (v, t))

/-- Temporal boundary edges of the slab, by step. -/
def temporalCut (σ : V × Fin (L + 1) → Bool) : Finset (Sym2 (V × Fin (L + 1))) :=
  univ.biUnion fun s : Fin L =>
    (univ.filter fun v => σ (v, s.castSucc) ≠ σ (v, s.succ)).image fun v => tE L v s

lemma cut_split (σ : V × Fin (L + 1) → Bool) :
    cutSet (slab G L) σ = spatialCut G L σ ∪ temporalCut L σ := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨u, a⟩ := x
    obtain ⟨w, b⟩ := y
    rw [mem_cutSet_iff, mem_union, spatialCut, temporalCut, mem_biUnion, mem_biUnion]
    simp only [mem_univ, true_and, mem_image, mem_filter]
    rw [boxProd_adj, pathGraph_adj]
    constructor
    · rintro ⟨hadj, hne⟩
      rcases hadj with ⟨hG, hab⟩ | ⟨hp, huw⟩
      · simp only at hab hG
        subst hab
        left
        refine ⟨a, s(u, w), ?_, rfl⟩
        rw [mem_cutSet_iff]; exact ⟨hG, hne⟩
      · simp only at hp huw
        subst huw
        right
        rcases hp with h | h
        · have h1 : (⟨a.val, by omega⟩ : Fin L).castSucc = a := Fin.ext rfl
          have h2 : (⟨a.val, by omega⟩ : Fin L).succ = b := Fin.ext (by simp [h])
          refine ⟨⟨a.val, by omega⟩, u, ?_, ?_⟩
          · rw [h1, h2]; exact hne
          · rw [tE, h1, h2]
        · have h1 : (⟨b.val, by omega⟩ : Fin L).castSucc = b := Fin.ext rfl
          have h2 : (⟨b.val, by omega⟩ : Fin L).succ = a := Fin.ext (by simp [h])
          refine ⟨⟨b.val, by omega⟩, u, ?_, ?_⟩
          · rw [h1, h2]; exact Ne.symm hne
          · rw [tE, h1, h2, Sym2.eq_swap]
    · rintro (⟨t, e, he, hmap⟩ | ⟨s, v, hv, hte⟩)
      · induction e using Sym2.ind with
        | h u' w' =>
          rw [mem_cutSet_iff] at he
          rw [Sym2.map_mk, Sym2.eq_iff] at hmap
          rcases hmap with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Prod.mk.injEq] at h1 h2
            obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
            exact ⟨Or.inl ⟨he.1, rfl⟩, he.2⟩
          · simp only [Prod.mk.injEq] at h1 h2
            obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
            exact ⟨Or.inl ⟨he.1.symm, rfl⟩, Ne.symm he.2⟩
      · simp only [tE, Sym2.eq_iff, Prod.mk.injEq] at hte
        rcases hte with ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨Or.inr ⟨Or.inl (by simp), rfl⟩, hv⟩
        · exact ⟨Or.inr ⟨Or.inr (by simp), rfl⟩, Ne.symm hv⟩

omit [Fintype V] [DecidableEq V] in
lemma tE_inj {v v' : V} {s s' : Fin L} (h : tE L v s = tE L v' s') : v = v' ∧ s = s' := by
  simp only [tE, Sym2.eq_iff, Prod.mk.injEq] at h
  rcases h with ⟨⟨h1, h2⟩, -, -⟩ | ⟨⟨h1, h2⟩, -, h3⟩
  · exact ⟨h1, Fin.castSucc_injective _ h2⟩
  · exfalso
    have := congrArg Fin.val h2; have := congrArg Fin.val h3; simp at *; omega

lemma card_spatialCut (σ : V × Fin (L + 1) → Bool) :
    (spatialCut G L σ).card = ∑ t, cost G (slice σ t) := by
  rw [spatialCut, card_biUnion]
  · refine sum_congr rfl fun t _ => ?_
    rw [card_image_of_injective _ (Sym2.map.injective fun x y h => (Prod.ext_iff.mp h).1)]
    rfl
  · intro t _ t' _ htt'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [mem_image] at he he'
    obtain ⟨e1, -, rfl⟩ := he
    obtain ⟨e2, -, h2⟩ := he'
    induction e1 using Sym2.ind with
    | h x y =>
      induction e2 using Sym2.ind with
      | h x' y' =>
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h2
        rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ <;> exact htt' (Prod.ext_iff.mp h).2.symm

lemma card_temporalCut (σ : V × Fin (L + 1) → Bool) :
    (temporalCut L σ).card = ∑ s : Fin L, ham (slice σ s.castSucc) (slice σ s.succ) := by
  rw [temporalCut, card_biUnion]
  · refine sum_congr rfl fun s _ => ?_
    rw [card_image_of_injective _ (fun v v' h => (tE_inj L h).1)]
    rfl
  · intro s _ s' _ hss'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [mem_image] at he he'
    obtain ⟨v, -, rfl⟩ := he
    obtain ⟨v', -, h⟩ := he'
    exact hss' (tE_inj L h).2.symm

lemma disjoint_cuts (σ : V × Fin (L + 1) → Bool) :
    Disjoint (spatialCut G L σ) (temporalCut L σ) := by
  rw [Finset.disjoint_left]
  intro e he he'
  rw [spatialCut, mem_biUnion] at he
  rw [temporalCut, mem_biUnion] at he'
  obtain ⟨t, -, he⟩ := he
  obtain ⟨s, -, he'⟩ := he'
  rw [mem_image] at he he'
  obtain ⟨e1, -, rfl⟩ := he
  obtain ⟨v, -, h⟩ := he'
  induction e1 using Sym2.ind with
  | h x y =>
    simp only [tE, Sym2.map_mk, Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨⟨-, h1⟩, -, h2⟩ | ⟨⟨-, h1⟩, -, h2⟩
    · have := congrArg Fin.val h1; have := congrArg Fin.val h2; simp at *; omega
    · have := congrArg Fin.val h1; have := congrArg Fin.val h2; simp at *; omega

/-- **Cut decomposition.** -/
theorem cut_decomp (σ : V × Fin (L + 1) → Bool) :
    (cutSet (slab G L) σ).card =
      ∑ t, cost G (slice σ t) + ∑ s : Fin L, ham (slice σ s.castSucc) (slice σ s.succ) := by
  rw [cut_split, card_union_of_disjoint (disjoint_cuts G L σ), card_spatialCut, card_temporalCut]

/-- Slab configurations are histories of slice states. -/
def histEquiv : (V × Fin (L + 1) → Bool) ≃ (Fin (L + 1) → V → Bool) where
  toFun σ t v := σ (v, t)
  invFun h p := h p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- The PM transfer matrix. -/
noncomputable def transfer (q : ℝ) : Matrix (V → Bool) (V → Bool) ℝ :=
  fun s s' => Real.sqrt q ^ cost G s * q ^ ham s s' * Real.sqrt q ^ cost G s'

/-- The free end vector. -/
noncomputable def v₀ (q : ℝ) (s : V → Bool) : ℝ := Real.sqrt q ^ cost G s

omit [DecidableEq V] in
lemma transfer_symm (q : ℝ) : Matrix.IsSymm (transfer G q) := by
  ext s s'
  simp only [Matrix.transpose_apply, transfer, ham]
  rw [show (univ.filter fun v => s' v ≠ s v) = univ.filter fun v => s v ≠ s' v by
    ext v; simp [ne_comm]]
  ring

/-- **The slab sum is a transfer-matrix product.** -/
theorem slab_transfer {q : ℝ} (hq : 0 ≤ q) (f g : (V → Bool) → ℝ) :
    (∑ σ : V × Fin (L + 1) → Bool,
        f (slice σ 0) * g (slice σ (Fin.last L)) * q ^ (cutSet (slab G L) σ).card) =
      (fun s => v₀ G q s * f s) ⬝ᵥ ((transfer G q).mulVec)^[L] (fun s => v₀ G q s * g s) := by
  rw [TransferHistory.power_eq_history, ← (histEquiv L).symm.sum_comp]
  refine sum_congr rfl fun h _ => ?_
  have hr : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have hw := TransferHistory.pm_weight hr (cost G) ham L h
  have hσ : ∀ t, slice ((histEquiv L).symm h) t = h t := fun _ => rfl
  rw [cut_decomp, hσ, hσ]
  simp only [hσ]
  rw [← hw]
  simp only [transfer, v₀]
  ring

end PMAction.MassGap.TransferSlab
