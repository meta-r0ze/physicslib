import PMAction.Machine.CarrierClassBundle

/-!
# All three glue classes are admitted

E8's carriers fall into three glue classes. `CarrierClassBundle` gives each class its own native
amplitude space and the same observed vacuum Hamiltonian, as "a consistent representation route,
rather than a selection of three physical generations". This file adds the selection.

* `observed_class_symmetric`: the observed vacuum generator is unchanged when the classes are
  permuted. No price built from it distinguishes one class from another.
* Persistence selects by price (`PersistenceSelection`). Say a class is admitted when its carriers
  occur in some most-persistent configuration. A class permutation maps configurations to
  configurations of the same price, so it maps most-persistent ones to most-persistent ones, and
  the admitted set `S` is invariant under every permutation.
* `invariant_subsets`: the only permutation-invariant sets of classes are `∅` and all three.
* `all_classes_admitted`: since carriers exist (`S` nonempty), all three classes are admitted.

Premises: admission defined through most-persistent configurations, and prices that depend on
the classes only through the observed generator. Whether each admitted class is one physical
generation is Paper IV's identification.
-/

namespace PMAction.ClassAdmission
open Matrix CarrierClassBundle

/-- **Class symmetry of the observed vacuum.** -/
theorem observed_class_symmetric (σ : Equiv.Perm (Fin 3)) (k : Fin 3 → ℝ) (δ : ℝ)
    (c d : Fin 3) (i j : ConcreteFermion.Sites) :
    observedGenerator k δ ⟨σ c, i⟩ ⟨σ d, j⟩ = observedGenerator k δ ⟨c, i⟩ ⟨d, j⟩ := by
  unfold observedGenerator
  by_cases h : c = d
  · subst h
    simp
  · simp [blockDiagonal'_apply, h, σ.injective.ne h]

/-- **The invariant sets of classes.** -/
theorem invariant_subsets :
    ∀ S : Finset (Fin 3), (∀ σ : Equiv.Perm (Fin 3), S.map σ.toEmbedding = S) →
      S = ∅ ∨ S = Finset.univ := by
  decide

/-- **All three classes are admitted.** -/
theorem all_classes_admitted (S : Finset (Fin 3))
    (hsym : ∀ σ : Equiv.Perm (Fin 3), S.map σ.toEmbedding = S) (hne : S.Nonempty) :
    S = Finset.univ := by
  rcases invariant_subsets S hsym with h | h
  · exact absurd h hne.ne_empty
  · exact h

end PMAction.ClassAdmission
