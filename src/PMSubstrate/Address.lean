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
    push Not at hc
    exact (Set.infinite_univ (α := ℕ)) ((Finset.finite_toSet _).subset (fun k _ => hc k))
  exact hk ((hle Submodule.mem_top : (Finsupp.single k 1 : ℕ →₀ ℤ) ∈ T)
    (Finsupp.mem_support_iff.mpr (by simp)))

/-- Coordinate-sum `σ x = Σ xᵢ`, a `ℤ`-linear functional. -/
noncomputable def coordSum : (ℕ →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ (fun _ : ℕ => (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

/-- **The infinite-rank even lattice** `D_∞ = {x ∈ ℤ^(∞) : Σ xᵢ even}`. -/
def DInf : Submodule ℤ (ℕ →₀ ℤ) :=
  Submodule.comap coordSum (Submodule.span ℤ ({2} : Set ℤ))

/-- **Bit-addressing holds for `D_∞`.** `2·x ∈ D_∞` for every ambient `x`, i.e. `2·(D_∞*) ⊆ D_∞`
(the ambient `ℤ^(∞)` is `D_∞*`, since the standard form on `ℤ^(∞) ⊆ ℓ²` is self-dual). -/
theorem two_smul_mem_DInf (x : ℕ →₀ ℤ) : (2 : ℤ) • x ∈ DInf := by
  change coordSum ((2 : ℤ) • x) ∈ Submodule.span ℤ ({2} : Set ℤ)
  rw [map_smul]
  exact Submodule.mem_span_singleton.mpr ⟨coordSum x, by simp [smul_eq_mul, mul_comm]⟩

/-- `D_∞` has infinite rank (it contains `e₀ + e_k` for every `k`), so it is not finitely
generated. (Same support argument as `finsupp_not_finite_generated`.) -/
theorem DInf_not_finite : ¬ Module.Finite ℤ DInf := by
  intro h
  obtain ⟨s, hs⟩ := h.fg_top
  let U : Finset ℕ := s.biUnion fun g : DInf => (g : ℕ →₀ ℤ).support
  let T : Submodule ℤ (ℕ →₀ ℤ) :=
    { carrier := {x | x.support ⊆ U}
      zero_mem' := by simp
      add_mem' := fun hx hy =>
        (Finsupp.support_add (g₁ := _) (g₂ := _)).trans (Finset.union_subset hx hy)
      smul_mem' := fun a _ hx => (Finsupp.support_smul (b := a)).trans hx }
  have hspan : Submodule.span ℤ ((Submodule.subtype DInf) '' (s : Set DInf)) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact Finset.subset_biUnion_of_mem (fun g : DInf => (g : ℕ →₀ ℤ).support) hg
  have hDInf_le : DInf ≤ T := by
    have heq : DInf = Submodule.span ℤ ((Submodule.subtype DInf) '' (s : Set DInf)) := by
      have hmap : (⊤ : Submodule ℤ DInf).map (Submodule.subtype DInf) = DInf :=
        Submodule.map_subtype_top DInf
      calc DInf = (⊤ : Submodule ℤ DInf).map (Submodule.subtype DInf) := hmap.symm
        _ = (Submodule.span ℤ (s : Set DInf)).map (Submodule.subtype DInf) := by rw [← hs]
        _ = Submodule.span ℤ ((Submodule.subtype DInf) '' (s : Set DInf)) :=
              Submodule.map_span _ _
    rw [heq]; exact hspan
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k ∉ U ∪ {0} := by
    by_contra hc
    push Not at hc
    exact (Set.infinite_univ (α := ℕ))
      ((Finset.finite_toSet (U ∪ {0})).subset (fun k _ => hc k))
  have hmemD : (Finsupp.single 0 1 + Finsupp.single k 1 : ℕ →₀ ℤ) ∈ DInf := by
    change coordSum (Finsupp.single 0 1 + Finsupp.single k 1) ∈ Submodule.span ℤ ({2} : Set ℤ)
    rw [map_add, show coordSum (Finsupp.single 0 (1 : ℤ)) = 1 by simp [coordSum],
      show coordSum (Finsupp.single k (1 : ℤ)) = 1 by simp [coordSum],
      show (1 : ℤ) + 1 = 2 by norm_num]
    exact Submodule.subset_span (Set.mem_singleton (2 : ℤ))
  have hk_supp : k ∈ (Finsupp.single 0 1 + Finsupp.single k 1 : ℕ →₀ ℤ).support :=
    Finsupp.mem_support_iff.mpr (by
      rw [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by rintro rfl; exact hk (by simp))]
      norm_num)
  exact hk (Finset.mem_union_left _ (hDInf_le hmemD hk_supp))

end PMSubstrate.Address
