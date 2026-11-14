import PMAction.InertiaStability
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Congruence for the nonsingular Hermitian matrices used by the Wilson certificate.
The complex pencil from the identity to the change of basis is singular only at
finitely many parameters. Its regular parameter set is connected, where the
existing local constancy theorem applies. -/
noncomputable section
namespace PMAction.InertiaCertificate
open Matrix Polynomial PMAction.InertiaStability

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem negCount_congruence {A : Matrix n n ℂ} (hA : A.IsHermitian) (ha : A.det ≠ 0)
    (Q : Matrix n n ℂ) (hq : Q.det ≠ 0) :
    negCount (isHermitian_conjTranspose_mul_mul Q hA) = negCount hA := by
  let F (z : ℂ) := (1 : Matrix n n ℂ) + z • (Q - 1)
  let P := ((1 : Matrix n n (Polynomial ℂ)) + (X : Polynomial ℂ) • (Q - 1).map C).det
  have heval (z : ℂ) : P.eval z = (F z).det := by
    simp only [P, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [F, hij, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
    exact mul_comm _ _
  have hzero : F 0 = 1 := by simp [F]
  have hone : F 1 = Q := by simp [F]
  have hp : P ≠ 0 := by
    intro h
    simpa [h, hzero] using heval 0
  let U := ({z : ℂ | P.IsRoot z} : Set ℂ)ᶜ
  have regular (z : ℂ) : z ∈ U ↔ (F z).det ≠ 0 := by
    change ¬ P.eval z = 0 ↔ _
    rw [heval]
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    ((Polynomial.finite_setOfPred_isRoot hp).countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  let H (z : U) := (F z.val)ᴴ * A * F z.val
  have herm (z : U) : (H z).IsHermitian := isHermitian_conjTranspose_mul_mul _ hA
  have inv (z : U) : (H z).det ≠ 0 := by
    have hz := (regular z.val).mp z.property
    simp [H, det_mul, det_conjTranspose, hz, ha]
  have cont : Continuous H := by unfold H F; fun_prop
  let z0 : U := ⟨0, (regular 0).mpr (by simp [hzero])⟩
  let z1 : U := ⟨1, (regular 1).mpr (by simpa [hone] using hq)⟩
  have eq := (negCount_locallyConstant H cont herm inv).apply_eq_of_preconnectedSpace z1 z0
  simpa [H, z0, z1, hone, hzero] using eq

end PMAction.InertiaCertificate
