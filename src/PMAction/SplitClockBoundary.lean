import PMAction.SplitCovariance
import PMAction.StateIdentification

/-! An exact finite-tick obstruction for the supplied vacuum-preserving split.
The diagnostic tick π is in generator units. It is not a clock calibration. -/
noncomputable section
namespace PMAction.SplitClockBoundary
open Matrix ConcreteFermion VacuumSplit NormedSpace
open scoped Matrix.Norms.Operator
abbrev M := Matrix Sites Sites ℂ

def other : M := (2 : ℂ) • wall + SplitCovariance.P8

set_option maxHeartbeats 4000000 in
lemma relations : other * other = 1 ∧
    SplitCovariance.P8 * other = other * SplitCovariance.P8 := by
  constructor <;> ext i j <;> cases i <;> cases j <;>
    rename_i i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [other, SplitCovariance.P8, wall, hamiltonian, DomainWallSpectrum.H,
      DomainWallSpectrum.momentum, DomainWallSpectrum.hop, DomainWallSpectrum.back,
      DomainWallSpectrum.plus, DomainWallSpectrum.minus, beta, gamma,
      mul_apply, vecMul, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three]

lemma coin_pi : wallCoin Real.pi = SplitCovariance.P8 * other := by
  let z : ℂ := -Complex.I * (Real.pi / 2 : ℝ)
  have decomp : (-Complex.I * (Real.pi : ℂ)) • wall =
      z • (-SplitCovariance.P8) + z • other := by
    dsimp [z, other]
    push_cast
    module
  have comm : Commute (z • (-SplitCovariance.P8)) (z • other) := by
    change (z • _) * (z • _) = _
    simp only [smul_mul_smul_comm, neg_mul, mul_neg, relations.2]
  rw [wallCoin, decomp, Matrix.exp_add_of_commute _ _ comm]
  have rot (G : M) (hG : G * G = 1) :
      exp (z • G) = (-Complex.I) • G := by
    have hz : z = Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ) := by dsimp [z]; push_cast; ring
    rw [hz, NativeObservation.exp_involution G hG]
    simp [LocalUnitary.rotation]
  rw [rot _ (by simp [SplitCovariance.P8_involution]), rot _ relations.1]
  simp [smul_smul, Complex.I_mul_I]

lemma update_pi (k : Fin 3 → ℝ) : momentumUpdate k Real.pi = wallCoin Real.pi := by
  simp [momentumUpdate, onsiteCoin, rotation, LocalUnitary.rotation,
    show (3 : ℕ) = 2 + 1 from rfl, pow_succ]

set_option maxHeartbeats 4000000 in
theorem noncommuting :
    ¬ Commute (momentumUpdate ![Real.pi/2,0,0] Real.pi)
      (hamiltonian ![Real.pi/2,0,0] (DomainWallSpectrum.wilson ![Real.pi/2,0,0])) := by
  intro h
  have he := congrFun (congrFun h.eq (.inl 0)) (.inl 2)
  rw [update_pi, coin_pi] at he
  norm_num [other, SplitCovariance.P8, wall, hamiltonian, DomainWallSpectrum.H,
    DomainWallSpectrum.momentum, DomainWallSpectrum.wilson, DomainWallSpectrum.hop,
    DomainWallSpectrum.back, DomainWallSpectrum.plus, DomainWallSpectrum.minus, beta, gamma, alpha,
    mul_apply, vecMul, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three] at he
/-- At the diagnostic tick no rescaling of Hamiltonian time repairs the
mismatch. Every scalar multiple of H has an exponential commuting with H. -/
theorem no_hamiltonian_time (z : ℂ) :
    momentumUpdate ![Real.pi/2,0,0] Real.pi ≠
      exp (z • hamiltonian ![Real.pi/2,0,0]
        (DomainWallSpectrum.wilson ![Real.pi/2,0,0])) := by
  intro h
  apply noncommuting
  rw [h]
  exact ((Commute.refl (hamiltonian ![Real.pi/2,0,0]
    (DomainWallSpectrum.wilson ![Real.pi/2,0,0]))).smul_left z).exp_left

end PMAction.SplitClockBoundary
