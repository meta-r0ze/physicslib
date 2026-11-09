import PMSubstrate.Translation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The additive address structure and the integral quadratic cost (S1)

The substrate's state space is `ℤⁿ` carrying an integral symmetric quadratic cost. This module
**derives** that structure from additive-address premises instead of assuming it:

* `integer_coordinates`: a finitely generated, torsion-free additive group is `ℤⁿ` — the
  additive **discrete address structure**.
* `integer_gram_representation`: an integer-valued symmetric bilinear cost has an integral
  Gram representation `B x y = e x ⬝ᵥ (A *ᵥ e y)` — the **integral quadratic cost**.
* `finite_budget_gram`: finite cost sublevels force that Gram positive definite, i.e. Finiteness
  (`Geometric.finite`) is `A.PosDef`.

The remaining inputs are the algebraic premises themselves — an additive address group, finite
generation, torsion-freeness, and an integer symmetric bilinear cost. These are the "independently
specified vacuum constraints"; **given** them, the lattice and the quadratic cost are consequences,
not choices. Counterexamples showing the premises are not themselves forced by bare persistence
live off the main path in `PMSubstrate.Research` (`ConstraintFoundations`); in particular a
finite-budget reversible cost does not by itself give the T or S theta laws.
-/

noncomputable section
namespace PMSubstrate.Address
open Matrix

/-- **Finite generations + additive translations + no torsion ⇒ integer coordinates.** A finitely
generated, torsion-free additive group is a free `ℤ`-module, i.e. `ℤⁿ`. -/
theorem integer_coordinates (M : Type*) [AddCommGroup M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M] :
    ∃ n : ℕ, Nonempty (M ≃ₗ[ℤ] (Fin n → ℤ)) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  exact ⟨n, ⟨b.equivFun⟩⟩

/-- **The integral quadratic cost.** An integer-valued symmetric bilinear cost on a finitely
generated, torsion-free additive address group has an integral Gram representation. -/
theorem integer_gram_representation (M : Type*) [AddCommGroup M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hs : ∀ x y, B x y = B y x) :
    ∃ n : ℕ, ∃ e : M ≃ₗ[ℤ] (Fin n → ℤ),
      ∃ A : Matrix (Fin n) (Fin n) ℤ,
        A.IsSymm ∧ ∀ x y, B x y = e x ⬝ᵥ (A *ᵥ e y) := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  refine ⟨n, b.equivFun, LinearMap.BilinForm.toMatrix b B, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply]
    exact hs (b j) (b i)
  · intro x y
    simpa only [Module.Basis.equivFun_apply] using
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B x y

/-- **Finiteness forces positive definiteness.** Finite cost sublevels make that Gram matrix
positive definite — the `Geometric.finite` postulate rewritten as `A.PosDef`. -/
theorem finite_budget_gram (M : Type*) [AddCommGroup M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hs : ∀ x y, B x y = B y x)
    (hf : ∀ c : ℤ, ({x : M | B x x ≤ c}).Finite) :
    ∃ n : ℕ, ∃ e : M ≃ₗ[ℤ] (Fin n → ℤ),
      ∃ A : Matrix (Fin n) (Fin n) ℤ,
        (A.map (Int.cast : ℤ → ℝ)).PosDef ∧
        ∀ x y, B x y = e x ⬝ᵥ (A *ᵥ e y) := by
  obtain ⟨n, e, A, hsym, he⟩ := integer_gram_representation M B hs
  refine ⟨n, e, A, ?_, he⟩
  apply (Translation.posDef_iff_finite_levels hsym).mpr
  intro c
  refine ((hf c).image e).subset ?_
  intro z hz
  refine ⟨e.symm z, ?_, by simp⟩
  change B (e.symm z) (e.symm z) ≤ c
  rw [he]
  simpa using hz

/-- **Finiteness does not force finite generation.** The finite-support group `ℤ^{(∞)}` (`ℕ →₀ ℤ`)
has a positive-definite integral form (`Σ xᵢ²`) with **finite cost sublevels**, yet is **not finitely
generated**. So the address lattice `ℤⁿ` (Paper I's Postulate L) is not a consequence of Finiteness:
a finite description admits infinite-rank addresses. The load-bearing extra premise is
bit-addressing (`2Λ* ⊆ Λ`, Postulate A), which `ℤ^{(∞)}` fails — the content of
`PMSubstrate.RequirementMap.S1_residual`. -/
theorem finsupp_not_finite_generated : ¬ Module.Finite ℤ (ℕ →₀ ℤ) := by
  intro h
  obtain ⟨s, hs⟩ := h.fg_top
  let T : Submodule ℤ (ℕ →₀ ℤ) :=
    { carrier := {x | x.support ⊆ s.biUnion Finsupp.support}
      zero_mem' := by simp
      add_mem' := fun hx hy =>
        (Finsupp.support_add (g₁ := _) (g₂ := _)).trans (Finset.union_subset hx hy)
      smul_mem' := fun a _ hx => (Finsupp.support_smul (b := a)).trans hx }
  have hle : (⊤ : Submodule ℤ (ℕ →₀ ℤ)) ≤ T := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    show x.support ⊆ s.biUnion Finsupp.support
    exact Finset.subset_biUnion_of_mem Finsupp.support hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k ∉ s.biUnion Finsupp.support := by
    by_contra hc
    push_neg at hc
    exact (Set.infinite_univ (α := ℕ)) ((Finset.finite_toSet _).subset (fun k _ => hc k))
  exact hk ((hle Submodule.mem_top : (Finsupp.single k 1 : ℕ →₀ ℤ) ∈ T)
    (Finsupp.mem_support_iff.mpr (by simp)))

end PMSubstrate.Address
