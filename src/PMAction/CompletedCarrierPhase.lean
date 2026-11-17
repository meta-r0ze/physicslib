import PMAction.RootCliffordCompletion

/-!
# A completed common i phase from the enlarged root circuit family

The three balanced diagonal involutions gamma, alpha_2, and a primitive-root
conjugate of gamma multiply to identity. Their completed three-quarter rotations
therefore multiply to i on the odd sector and identity on every even mode.
This uses composite completed circuits, so the four-root-family obstruction in
EvenRootPhase still holds. No lazy phase is assigned to a composite permutation.

All programs are class-blind. Coherent root-phase admission and a common rate
remain the existing inputs; durations and prices of the longer programs are not
identified with their output angles. No extra carrier bank is allocated.
-/
noncomputable section
namespace PMAction.CompletedCarrierPhase
open Matrix CarrierEvents CarrierParity RootCliffordCompletion PairedRootFlip
open scoped Matrix.Norms.Operator

def diagonal : Matrix (Fin 4) (Fin 4) ℂ := R 2 2 * ConcreteFermion.gamma * (R 2 2)ᴴ

def thirdPulse (c : Fin 3) (p t : ℝ) :=
  swapPulse c p 2 2 * gammaPulse c p t * (swapPulse c p 2 2)ᴴ

lemma rotation_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    (S B : Matrix n n ℂ) (hu : S*Sᴴ = 1) (t : ℝ) :
    S * LocalUnitary.rotation B t * Sᴴ = LocalUnitary.rotation (S*B*Sᴴ) t := by
  simp only [LocalUnitary.rotation, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hu]

lemma third_completed (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    thirdPulse c p t = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation diagonal (RootTransferPhase.gap p*t)) := by
  have hu : R 2 2 * (R 2 2)ᴴ = 1 :=
    (observed_unitary _ (isometry c) _ _ (swap_observed c p 2 2 hp hp1) (swap_unitary c p 2 2)).2
  rw [thirdPulse, gamma_completed c p t hp hp1,
    conjugate_completion _ _ _ _ (swap_observed c p 2 2 hp hp1) (swap_unitary c p 2 2),
    rotation_conjugate _ _ hu]
  rfl

lemma diagonal_product : ConcreteFermion.gamma * ConcreteFermion.alpha 2 * diagonal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonal, R, RZ, axisPerm, Equiv.swap_apply_def, OrthogonalRootPhase.realMatrix,
      ConcreteFermion.gamma, ConcreteFermion.alpha, mul_apply, conjTranspose_apply, Fin.sum_univ_four]

lemma three_quarters (B : Matrix (Fin 4) (Fin 4) ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    LocalUnitary.rotation B (RootTransferPhase.gap p*(3*RootTransferPhase.quarterTime p)) =
      -Complex.I • B := by
  have ht : RootTransferPhase.gap p*(3*RootTransferPhase.quarterTime p) = - (Real.pi/2) + 2*Real.pi := by
    linarith [quarter_angle p hp hp1]
  simp [LocalUnitary.rotation, ht]

/-- A fixed common program in every glue class. -/
def phaseI (c : Fin 3) (p : ℝ) :=
  gammaPulse c p (3*RootTransferPhase.quarterTime p) *
    alphaPulse c p (3*RootTransferPhase.quarterTime p) 2 *
    thirdPulse c p (3*RootTransferPhase.quarterTime p)

/-- The complete common i phase, including its action on all invisible modes. -/
theorem phase_completed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    phaseI c p = IsometricDynamics.extend (embedding c)
      (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
  rw [phaseI, gamma_completed c p _ hp hp1, alpha_completed c p _ 2 hp hp1,
    third_completed c p _ hp hp1, three_quarters _ p hp hp1, three_quarters _ p hp hp1,
    three_quarters _ p hp hp1, ← IsometricDynamics.extend_mul _ (isometry c),
    ← IsometricDynamics.extend_mul _ (isometry c)]
  congr 1
  simp only [smul_mul_smul_comm, diagonal_product]
  norm_num [Complex.I_sq]

lemma scalar_i_unitary : (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ∈ unitary _ := by
  constructor <;> simp [smul_smul]

theorem phase_unitary (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    phaseI c p ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  rw [phase_completed c p hp hp1]
  exact IsometricDynamics.unitary _ (isometry c) _ scalar_i_unitary

theorem phase_fixes_even (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    phaseI c p * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  rw [phase_completed c p hp hp1]
  exact completed_fixes_even c _

/-- Quarter-turn rotations become the actual completed Hermitian generators
when their common odd i factor is removed by the completed inverse phase. -/
def reflection (c : Fin 3) (p : ℝ) (g : Generator) :=
  (phaseI c p)ᴴ * instruction c p (RootTransferPhase.quarterTime p) g

theorem reflection_completed (c : Fin 3) (p : ℝ) (g : Generator)
    (hp : 0 < p) (hp1 : p < 1/2) :
    reflection c p g = IsometricDynamics.extend (embedding c) (coordinate g) := by
  rw [reflection, phase_completed c p hp hp1, IsometricDynamics.extend_star,
    instruction_completed c p _ g hp hp1, quarter_angle p hp hp1,
    ← IsometricDynamics.extend_mul _ (isometry c)]
  congr 1
  simp [LocalUnitary.rotation, smul_smul]

end PMAction.CompletedCarrierPhase
