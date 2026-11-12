import PMAction.WilsonSplit
import PMAction.ClockLedger

/-!
# Admission of the coherent substrate dynamics

REVIEW B.2 and B.5 come to one question: which local amplitude factors does the substrate
implement? The split update's factors are exponentials of native Hermitian generators
(`StateIdentification`'s `NativeSplit`). This file states the admission rule and checks the
factors against it.

**Rule (Persistence Mechanics).** A factor is admitted when it conserves the total amplitude
(unitary, so population is conserved: `SplitUpdate.update_population`), is local (its matrix is
supported on the neighbour relation, so one tick reads a bounded stencil), and is priced (its
flags cost `toll·m` each, `ClockLedger.tick_cost`). Nothing in the survival law excludes a
conserving, local, priced factor, so admission is by default, as for the glue classes
(`ClassAdmission`); a factor is excluded only with a persistence reason.

* `Admitted`: unitary and supported on a given neighbour relation.
* `direction_admitted`: each directional rotation `cos τ + i sin τ N_j` is admitted on the
  neighbour relation of its axis.
* `coin_admitted`: the on-site coin `e^{−iτH₀}` is admitted on the identity relation.

The cost side needs no further statement: every factor has a flag cost (`repairCost` is defined
for every matrix), fixed in units by the electric calibration. What this does not settle: which
E8 root words the native generators come from (the microscopic hop of B.5).
-/

noncomputable section
namespace PMAction.Admission
open Matrix ConcreteFermion

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The admission rule's conditions:** unitary and local on the relation `R`. -/
structure Admitted (R : X → X → Prop) (A : Matrix (X × Sites) (X × Sites) ℂ) : Prop where
  isUnitary : A ∈ unitary (Matrix (X × Sites) (X × Sites) ℂ)
  isLocal : SplitUpdate.Supported R A

/-- **The directional rotations are admitted.** -/
theorem direction_admitted (e : Equiv.Perm X) (j : Fin 3) (τ : ℝ) :
    Admitted (SplitUpdate.Near e) (SplitUpdate.direction e j τ) :=
  ⟨SplitUpdate.direction_unitary e j τ, SplitUpdate.direction_supported e j τ⟩

/-- **The on-site coin is admitted.** -/
theorem coin_admitted (τ : ℝ) :
    Admitted Eq (SplitUpdate.onsite (X := X) (WilsonSplit.onsiteCoin τ)) :=
  ⟨SplitUpdate.onsite_unitary _ (WilsonSplit.onsiteCoin_unitary τ),
    SplitUpdate.onsite_supported _⟩

end PMAction.Admission
