import PMAction.MassGap.ContourGas

/-!
# History sums as weighted contour gases

`ContourGas.contour_gas_eq` identifies `Σ_{C even} q^|C|` with a contour gas. This file
generalizes it in two directions that the transfer-matrix argument needs.

* `contour_gas_weighted`: any **edge weight** `ω`. The sum of `Π_{e∈C} ω e` over even edge sets
  equals the polymer partition function of contours with activity `Π_{e∈γ} ω e`. Signs
  (`ω = −q` on some edges) encode parity observables, and `ω = 0` on an edge forbids it (pinned
  vacuum).
* `cutSet σ`: the boundary edges of a configuration; `cutSet_isCut`.
* `history_sum`: the sum over vacuum-rooted configurations of any function of the boundary equals
  the sum over even edge sets (the bijection of `ContourRepresentation`).

Together: `Σ_{σ, σ r = false} Π_{e ∈ cut σ} ω e` is a contour-gas partition function.
-/

namespace PMAction.MassGap.HistorySum
open Finset ContourRepresentation ContourGas

variable {X : Type*} [Fintype X] [DecidableEq X] (Γ : SimpleGraph X) [DecidableRel Γ.Adj]
  (plaq : Finset (Finset (Sym2 X)))

open Classical in
/-- **Weighted contour gas.** -/
theorem contour_gas_weighted (hconn : Γ.Connected) (r : X) (hgen : PlaquettesGenerate Γ plaq)
    (hplaq : ∀ P ∈ plaq, IsPlaquette Γ P) (ω : Sym2 X → ℝ) :
    (∑ C ∈ Γ.edgeFinset.powerset.filter (fun C => EvenCycles Γ C), ∏ e ∈ C, ω e) =
      PolymerConvergence.Z (Incompat Γ plaq) (fun γ => ∏ e ∈ γ.1, ω e) univ := by
  classical
  unfold PolymerConvergence.Z
  symm
  apply Finset.sum_nbij' (union Γ plaq) (comps Γ plaq)
  · intro I hI
    simp only [mem_filter, mem_powerset] at hI ⊢
    obtain ⟨h1, h2⟩ := union_even Γ plaq hI.2
    exact ⟨h2, h1⟩
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨subset_univ _, comps_independent Γ plaq C⟩
  · intro I hI
    simp only [mem_filter] at hI
    exact comps_union Γ plaq hI.2
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC
    exact union_comps Γ plaq hconn r hgen hplaq hC.1 hC.2
  · intro I hI
    simp only [mem_filter] at hI
    rw [union, prod_biUnion]
    intro a ha b hb hab
    by_contra hd
    exact hI.2 a ha b hb hab (Or.inl hd)

/-- The boundary edges of a configuration. -/
def cutSet (σ : X → Bool) : Finset (Sym2 X) :=
  Γ.edgeFinset.filter fun e => Sym2.lift ⟨fun a b => σ a != σ b, fun a b => by
    show (σ a != σ b) = (σ b != σ a)
    cases σ a <;> cases σ b <;> rfl⟩ e

omit [DecidableEq X] in
lemma mem_cutSet {σ : X → Bool} {u v : X} (h : Γ.Adj u v) :
    s(u, v) ∈ cutSet Γ σ ↔ σ u ≠ σ v := by
  simp [cutSet, h]

omit [DecidableEq X] in
lemma cutSet_isCut (σ : X → Bool) : IsCut Γ σ (cutSet Γ σ) :=
  fun _ _ h => mem_cutSet Γ h

omit [DecidableEq X] in
lemma cutSet_sub (σ : X → Bool) : cutSet Γ σ ⊆ Γ.edgeFinset := filter_subset _ _

omit [DecidableEq X] in
/-- An even edge set is the `cutSet` of the configuration it determines. -/
lemma cut_eq_cutSet {σ : X → Bool} {C : Finset (Sym2 X)} (hC : IsCut Γ σ C)
    (hCE : C ⊆ Γ.edgeFinset) : C = cutSet Γ σ := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    constructor
    · intro he
      have hadj : Γ.Adj u v := by
        have := hCE he; simpa using this
      exact (mem_cutSet Γ hadj).mpr ((hC u v hadj).mp he)
    · intro he
      have hadj : Γ.Adj u v := by
        have := cutSet_sub Γ σ he; simpa using this
      exact (hC u v hadj).mpr ((mem_cutSet Γ hadj).mp he)

open Classical in
/-- **History sum.** Summing any function of the boundary over vacuum-rooted configurations is
summing it over even edge sets. -/
theorem history_sum (hconn : Γ.Connected) (r : X) (F : Finset (Sym2 X) → ℝ) :
    (∑ σ ∈ univ.filter (fun σ : X → Bool => σ r = false), F (cutSet Γ σ)) =
      ∑ C ∈ Γ.edgeFinset.powerset.filter (fun C => EvenCycles Γ C), F C := by
  classical
  apply Finset.sum_nbij (cutSet Γ)
  · intro σ _
    simp only [mem_filter, mem_powerset]
    exact ⟨cutSet_sub Γ σ, cut_even (cutSet_isCut Γ σ)⟩
  · intro σ hσ τ hτ he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ hτ
    have hτ' : IsCut Γ τ (cutSet Γ σ) := by rw [he]; exact cutSet_isCut Γ τ
    exact potential_unique hconn (cutSet_isCut Γ σ) hτ' r (by rw [hσ, hτ])
  · intro C hC
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq] at hC
    obtain ⟨σ, hσr, hσ⟩ := exists_potential hconn r C hC.2
    refine ⟨σ, by simp [hσr], ?_⟩
    exact (cut_eq_cutSet Γ hσ hC.1).symm
  · intro σ _; rfl

end PMAction.MassGap.HistorySum
