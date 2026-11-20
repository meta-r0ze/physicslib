import PMElementaryParticles.PhaseToRecord
import PMKAutomaton.Machine.CarrierResponse
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Coherent ring step

A tick on `Fin n × (Unit ⊕ Unit)`:

1. direction `.inl` shifts the site forward by one, `.inr` shifts it backward;
2. at every site the certified encounter `compare (phase x)` acts on the two
directions.

The full-firing tick is `(1 ⊗ encounter x) * shift`.  It is unitary because the
shift is a permutation matrix and `encounter x` is unitary.  The momentum-block
dispersion is recorded in the script and in the docs; the Lean block proof is
not completed here.
-/

noncomputable section
namespace PMElementaryParticles.CoherentRing

open Matrix
open PMAction
open PMElementaryParticles.PhaseToRecord
open PMAction.CoherentComparisonRepair

/-- Direction-dependent site shift: `.inl` forward, `.inr` backward. -/
def ringShift (n : ℕ) : Equiv.Perm (Fin n × (Unit ⊕ Unit)) where
  toFun p :=
    match p.2 with
    | Sum.inl _ => (finRotate n p.1, Sum.inl ())
    | Sum.inr _ => ((finRotate n).symm p.1, Sum.inr ())
  invFun p :=
    match p.2 with
    | Sum.inl _ => ((finRotate n).symm p.1, Sum.inl ())
    | Sum.inr _ => (finRotate n p.1, Sum.inr ())
  left_inv p := by
    rcases p with ⟨x, d⟩
    cases d
    · apply Prod.ext
      · exact (finRotate n).symm_apply_apply x
      · rfl
    · apply Prod.ext
      · exact (finRotate n).apply_symm_apply x
      · rfl
  right_inv p := by
    rcases p with ⟨x, d⟩
    cases d
    · apply Prod.ext
      · exact (finRotate n).apply_symm_apply x
      · rfl
    · apply Prod.ext
      · exact (finRotate n).symm_apply_apply x
      · rfl

/-- Full-firing coherent tick: encounter at every site after the shift. -/
def ringTick (n : ℕ) (x : ℝ) :
    Matrix (Fin n × (Unit ⊕ Unit)) (Fin n × (Unit ⊕ Unit)) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) (encounter x) *
    (ringShift n).permMatrix ℂ

theorem ringTick_unitary (n : ℕ) (x : ℝ) :
    ringTick n x ∈ unitary (Matrix (Fin n × (Unit ⊕ Unit))
      (Fin n × (Unit ⊕ Unit)) ℂ) := by
  have hC : Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) (encounter x) ∈
      unitary (Matrix (Fin n × (Unit ⊕ Unit)) (Fin n × (Unit ⊕ Unit)) ℂ) :=
    Matrix.kronecker_mem_unitary (one_mem _) (encounter_unitary x)
  have hS : (ringShift n).permMatrix ℂ ∈ unitary
      (Matrix (Fin n × (Unit ⊕ Unit)) (Fin n × (Unit ⊕ Unit)) ℂ) :=
    PMAction.CarrierResponse.perm_unitary (ringShift n)
  exact Submonoid.mul_mem _ hC hS

end PMElementaryParticles.CoherentRing
