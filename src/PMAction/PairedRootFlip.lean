import PMAction.CarrierGateCompletion
import PMAction.Machine.OrthogonalRootPhase
import PMAction.StateIdentification

/-!
# A paired-root coherent flip with identity completion

Root pulses with opposite phase times can cancel their scalar terms and their
even-sector action. The paired-root construction uses actual D4 reflections,
not a phase assigned to a composite permutation. In the spinor class an extra
root-phase conjugation changes the relative sign of the two coordinate pairs.

All three carrier classes are treated here by a class-indexed circuit family.
`ClassBlindFlip` supplies a common class-blind echo from these same root phases;
neither construction selects the physical event law. The result concerns the complete scheduled pulse: intermediate
operations may move even modes. Coherent root phases, a common rate and a
schedule are inputs. Inverse parameters can be wrapped into a forward phase
period on the stated interval. Primitive prices, physical clock calibration
and selection as the native flip law remain open. The parameter controlling
the output angle is not the full circuit duration. No measured input is used.
-/
noncomputable section
namespace PMAction.PairedRootFlip
open Matrix CarrierEvents CarrierParity
open scoped Matrix.Norms.Operator

/-- Three coordinate partitions, obtained by exchanging axis 1 with a spatial axis. -/
def axisPerm (a : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap 1 a.succ

def rootEvent (c : Fin 3) (a : Fin 3) (j : Fin 4) : Equiv.Perm (Carrier c) :=
  permute c (axisPerm a) * OrthogonalRootPhase.event c j * permute c (axisPerm a)

def rootVector (a : Fin 3) (j : Fin 4) : Fin 4 → ℤ :=
  OrthogonalRootPhase.roots j ∘ axisPerm a

lemma root_certificate : ∀ c a j (v : Carrier c), vector (rootEvent c a j v) =
    PMSubstrate.ChannelSymmetry.refl (rootVector a j) (vector v) := by
  decide +kernel

lemma root_norm : ∀ a j, PMSubstrate.ChannelSymmetry.dot4
    (rootVector a j) (rootVector a j) = 2 := by decide +kernel

lemma root_twice : ∀ c a j, Function.Involutive (rootEvent c a j) := by
  unfold Function.Involutive
  decide +kernel

lemma root_commutes : ∀ c a i j (v : Carrier c),
    rootEvent c a i (rootEvent c a j v) = rootEvent c a j (rootEvent c a i v) := by
  decide +kernel

lemma root_antipode : ∀ c a j (v : Carrier c),
    rootEvent c a j (antipode c v) = antipode c (rootEvent c a j v) := by
  decide +kernel

def RZ (a : Fin 3) (j : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i k => OrthogonalRootPhase.realMatrix j (axisPerm a i) (axisPerm a k)
def R (a : Fin 3) (j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun i k => (RZ a j i k : ℂ)

lemma root_coordinates : ∀ c a j (v : Carrier c) i,
    vector (rootEvent c a j v) i = ∑ k, vector v k * RZ a j k i := by
  decide +kernel

theorem root_intertwines (c : Fin 3) (a : Fin 3) (j : Fin 4) :
    (rootEvent c a j).permMatrix ℂ * embedding c = embedding c * R a j := by
  ext v i
  change ((rootEvent c a j).permMatrix ℂ *ᵥ (fun w => embedding c w i)) v = _
  rw [permMatrix_mulVec]
  change scale * (vector (rootEvent c a j v) i : ℂ) = _
  have hc := congrArg (fun z : ℤ => (z : ℂ)) (root_coordinates c a j v i)
  push_cast at hc
  rw [hc, Finset.mul_sum]
  simp only [mul_apply, embedding, R]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem root_observed (c : Fin 3) (a : Fin 3) (j : Fin 4) :
    NativeObservation.Obs (embedding c) ((rootEvent c a j).permMatrix ℂ) (R a j) :=
  NativeSector.obs_of c (root_intertwines c a j)
    (NativeSector.perm_commute c _ (root_antipode c a j))

/-- Signs pair the actual root actions; class 1 needs a relative sign between coordinate pairs. -/
def sign (c : Fin 3) : Fin 4 → ℤ :=
  if c = 1 then ![1,-1,-1,1] else ![1,-1,1,-1]

def BZ (c : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ :=
  if c = 1 then !![0,0,1,0;0,0,0,-1;1,0,0,0;0,-1,0,0]
  else CarrierWeyl.realMatrix 0

def B (c : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => (BZ c i j : ℂ)

def signedRow (c : Fin 3) (v w : Carrier c) : ℤ :=
  ∑ j : Fin 4, sign c j * (if rootEvent c 1 j v = w then 1 else 0)

/-- Full-label certificate: the root combination is the compressed coordinate operator. -/
lemma compression_certificate : ∀ c (v w : Carrier c),
    4 * signedRow c v w = ∑ k : Fin 4, ∑ i : Fin 4,
      vector v i * BZ c i k * vector w k := by
  decide +kernel

/-- The paired native generator, including its action on every invisible label. -/
def G (c : Fin 3) : Matrix (Carrier c) (Carrier c) ℂ :=
  fun v w => (signedRow c v w : ℂ) / 2

theorem generator_roots (c : Fin 3) : G c = (1/2 : ℂ) •
    (∑ j : Fin 4, (sign c j : ℂ) • (rootEvent c 1 j).permMatrix ℂ) := by
  ext v w
  simp [G, signedRow, Matrix.sum_apply, Matrix.smul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, div_eq_mul_inv, mul_comm]

theorem generator_compressed (c : Fin 3) : G c = embedding c * B c * (embedding c)ᴴ := by
  ext v w
  have hc := congrArg (fun z : ℤ => (z : ℂ)) (compression_certificate c v w)
  push_cast at hc
  have ht (i k : Fin 4) : embedding c v i * B c i k * star (embedding c w k) =
      (1/8 : ℂ) * ((vector v i : ℂ) * (BZ c i k : ℂ) * (vector w k : ℂ)) := by
    simp only [embedding, B, star_mul, star_intCast]
    calc
      _ = (star scale * scale) *
          ((vector v i : ℂ) * (BZ c i k : ℂ) * (vector w k : ℂ)) := by ring
      _ = _ := by rw [scale_sq]
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
  simp_rw [ht]
  simp_rw [← Finset.mul_sum]
  change (signedRow c v w : ℂ) / 2 = _
  linear_combination hc / 8

lemma generator_commutes (c : Fin 3) (p : ℝ) (i j : Fin 4) :
    Commute (RootTransferPhase.generator (rootEvent c 1 i) p)
      (RootTransferPhase.generator (rootEvent c 1 j) p) := by
  have hp : (rootEvent c 1 i).permMatrix ℂ * (rootEvent c 1 j).permMatrix ℂ =
      (rootEvent c 1 j).permMatrix ℂ * (rootEvent c 1 i).permMatrix ℂ := by
    have h : rootEvent c 1 j * rootEvent c 1 i = rootEvent c 1 i * rootEvent c 1 j := by
      apply Equiv.ext
      intro v
      exact root_commutes c 1 j i v
    rw [← permMatrix_mul, ← permMatrix_mul, h]
  show _ * _ = _ * _
  simp only [RootTransferPhase.generator, InvolutionSpectral.minus,
    smul_mul_smul_comm, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [hp]
  module

def pulseExponent (c : Fin 3) (p t : ℝ) (j : Fin 4) : Matrix (Carrier c) (Carrier c) ℂ :=
  (((-((sign c j : ℝ)*t) : ℝ) : ℂ) * Complex.I) •
    RootTransferPhase.generator (rootEvent c 1 j) p

def blockPulse (c : Fin 3) (p t : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  RootTransferPhase.phase (rootEvent c 1 0) p ((sign c 0 : ℝ)*t) *
    RootTransferPhase.phase (rootEvent c 1 1) p ((sign c 1 : ℝ)*t) *
    RootTransferPhase.phase (rootEvent c 1 2) p ((sign c 2 : ℝ)*t) *
    RootTransferPhase.phase (rootEvent c 1 3) p ((sign c 3 : ℝ)*t)

theorem exp_four {n : Type*} [Fintype n] [DecidableEq n]
    (X : Fin 4 → Matrix n n ℂ) (h : ∀ i j, Commute (X i) (X j)) :
    NormedSpace.exp (X 0 + X 1 + X 2 + X 3) =
      NormedSpace.exp (X 0) * NormedSpace.exp (X 1) *
        NormedSpace.exp (X 2) * NormedSpace.exp (X 3) := by
  have h2 : Commute (X 0 + X 1) (X 2) := by
    show _ * _ = _ * _
    simp [add_mul, mul_add, (h 0 2).eq, (h 1 2).eq]
  have h3 : Commute (X 0 + X 1 + X 2) (X 3) := by
    show _ * _ = _ * _
    simp [add_mul, mul_add, (h 0 3).eq, (h 1 3).eq, (h 2 3).eq]
  rw [Matrix.exp_add_of_commute _ _ h3, Matrix.exp_add_of_commute _ _ h2,
    Matrix.exp_add_of_commute _ _ (h 0 1)]

/-- The scalar offsets cancel exactly for the mirrored root pulses. -/
theorem block_exponential (c : Fin 3) (p t : ℝ) : blockPulse c p t =
    NormedSpace.exp ((Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • G c) := by
  have hcomm : ∀ i j, Commute (pulseExponent c p t i) (pulseExponent c p t j) := by
    intro i j
    show _ * _ = _ * _
    simp only [pulseExponent, smul_mul_smul_comm]
    rw [(generator_commutes c p i j).eq, mul_comm]
  have hs : pulseExponent c p t 0 + pulseExponent c p t 1 +
      pulseExponent c p t 2 + pulseExponent c p t 3 =
      (Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • G c := by
    rw [generator_roots]
    simp only [pulseExponent, RootTransferPhase.generator, InvolutionSpectral.minus, Fin.sum_univ_four]
    fin_cases c <;> simp [sign, smul_sub, smul_smul] <;> module
  rw [← hs, exp_four _ hcomm]
  rfl

/-- Completed evolution follows from the full compressed generator, not an
assumed inert complement. The earlier single-pulse obstruction still applies. -/
theorem block_completed (c : Fin 3) (p t : ℝ) : blockPulse c p t =
    IsometricDynamics.extend (embedding c)
      (NormedSpace.exp ((Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • B c)) := by
  have hg : G c * embedding c = embedding c * B c := by
    rw [generator_compressed, Matrix.mul_assoc, Matrix.mul_assoc,
      isometry, Matrix.mul_one]
  have hP : G c * IsometricDynamics.complement (embedding c) = 0 := by
    rw [generator_compressed, Matrix.mul_assoc,
      IsometricDynamics.complement_right _ (isometry c), Matrix.mul_zero]
  have hA : blockPulse c p t * embedding c = embedding c *
      NormedSpace.exp ((Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • B c) := by
    rw [block_exponential]
    exact RectangularEvolution.scaled _ _ _ hg _
  apply (CompletionSelection.agreement_iff _ (isometry c) _ _ hA).mpr
  rw [block_exponential]
  have he := RectangularEvolution.scaled (G c) 0
    (IsometricDynamics.complement (embedding c)) (by simpa using hP)
    (Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ))
  simpa using he

/-! ## The phase conjugation needed for the spinor class -/

def factor (a : Fin 3) (j : Fin 4) (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  InvolutionSpectral.plus (R a j) + z • InvolutionSpectral.minus (R a j)

theorem root_phase_observed (c : Fin 3) (a : Fin 3) (j : Fin 4) (p t : ℝ) :
    NativeObservation.Obs (embedding c) (RootTransferPhase.phase (rootEvent c a j) p t)
      (factor a j (Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I))) := by
  rw [RootTransferPhase.phase_formula _ (root_twice c a j)]
  have hp := NativeObservation.smul (1/2 : ℂ)
    (NativeObservation.add NativeObservation.one (root_observed c a j))
  have hm := NativeObservation.smul (1/2 : ℂ)
    (NativeObservation.sub NativeObservation.one (root_observed c a j))
  exact NativeObservation.add hp (NativeObservation.smul _ hm)

lemma quarter_angle (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.gap p * RootTransferPhase.quarterTime p = Real.pi/2 := by
  have hn := (RootTransferPhase.gap_positive p hp hp1).ne'
  unfold RootTransferPhase.quarterTime
  field_simp

lemma quarter_coeff (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    Complex.exp (-(RootTransferPhase.gap p*RootTransferPhase.quarterTime p : ℝ)*Complex.I) =
      -Complex.I := by
  rw [quarter_angle p hp hp1]
  push_cast
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  ring

lemma inverse_quarter_coeff (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    Complex.exp (-(RootTransferPhase.gap p*(-RootTransferPhase.quarterTime p) : ℝ)*Complex.I) =
      Complex.I := by
  rw [mul_neg, quarter_angle p hp hp1]
  push_cast
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  ring

def S : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-Complex.I,0,0,0;0,1,0,0;0,0,Complex.I,0;0,0,0,1]

set_option maxHeartbeats 2000000 in
lemma conjugator_coordinates :
    factor 0 0 (-Complex.I) * factor 0 1 (-Complex.I) *
      factor 2 2 Complex.I * factor 2 3 Complex.I = S := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [factor, InvolutionSpectral.plus, InvolutionSpectral.minus, R, RZ,
      axisPerm, Equiv.swap_apply_def, OrthogonalRootPhase.realMatrix, mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_four, S]
  all_goals ring_nf
  all_goals norm_num

def conjugator (c : Fin 3) (p : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  RootTransferPhase.phase (rootEvent c 0 0) p (RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c 0 1) p (RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c 2 2) p (-RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c 2 3) p (-RootTransferPhase.quarterTime p)

theorem conjugator_observed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs (embedding c) (conjugator c p) S := by
  have h := NativeObservation.mul (NativeObservation.mul (NativeObservation.mul
    (root_phase_observed c 0 0 p (RootTransferPhase.quarterTime p))
    (root_phase_observed c 0 1 p (RootTransferPhase.quarterTime p)))
    (root_phase_observed c 2 2 p (-RootTransferPhase.quarterTime p)))
    (root_phase_observed c 2 3 p (-RootTransferPhase.quarterTime p))
  simpa only [conjugator, quarter_coeff p hp hp1, inverse_quarter_coeff p hp hp1,
    conjugator_coordinates] using h

theorem conjugator_unitary (c : Fin 3) (p : ℝ) :
    conjugator c p ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) :=
  mul_mem (mul_mem (mul_mem
    (RootTransferPhase.phase_unitary _ (root_twice c 0 0) _ _)
    (RootTransferPhase.phase_unitary _ (root_twice c 0 1) _ _))
    (RootTransferPhase.phase_unitary _ (root_twice c 2 2) _ _))
    (RootTransferPhase.phase_unitary _ (root_twice c 2 3) _ _)

/-- The inverse circuit is a word of the same root phases with reversed parameters. -/
theorem phase_adjoint {n : Type*} [Fintype n] [DecidableEq n]
    (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) :
    (RootTransferPhase.phase e p t)ᴴ = RootTransferPhase.phase e p (-t) := by
  rw [RootTransferPhase.phase, ← Matrix.exp_conjTranspose, RootTransferPhase.phase]
  congr 1
  simp [conjTranspose_smul, (RootTransferPhase.generator_hermitian e he p).eq]

lemma phase_add {n : Type*} [Fintype n] [DecidableEq n]
    (e : Equiv.Perm n) (p s t : ℝ) :
    RootTransferPhase.phase e p (s+t) = RootTransferPhase.phase e p s *
      RootTransferPhase.phase e p t := by
  have hc : Commute ((((-s : ℝ) : ℂ)*Complex.I) • RootTransferPhase.generator e p)
      ((((-t : ℝ) : ℂ)*Complex.I) • RootTransferPhase.generator e p) := by
    show _ * _ = _ * _
    simp only [smul_mul_smul_comm]
    rw [mul_comm]
  unfold RootTransferPhase.phase
  rw [show (((-(s+t) : ℝ) : ℂ)*Complex.I) • RootTransferPhase.generator e p =
      (((-s : ℝ) : ℂ)*Complex.I) • RootTransferPhase.generator e p +
      (((-t : ℝ) : ℂ)*Complex.I) • RootTransferPhase.generator e p by
        push_cast; module,
    Matrix.exp_add_of_commute _ _ hc]

lemma four_quarter_return {n : Type*} [Fintype n] [DecidableEq n]
    (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.phase e p (4*RootTransferPhase.quarterTime p) = 1 := by
  rw [RootTransferPhase.phase_formula e he]
  have hz : Complex.exp (-(RootTransferPhase.gap p*(4*RootTransferPhase.quarterTime p) : ℝ)*
      Complex.I) = 1 := by
    have ht : RootTransferPhase.gap p*(4*RootTransferPhase.quarterTime p) = 2*Real.pi := by
      nlinarith [quarter_angle p hp hp1]
    rw [ht]
    push_cast
    simp [neg_mul, Complex.exp_neg]
  rw [hz, one_smul, InvolutionSpectral.sum]

/-- An inverse pulse can use the remaining part of its forward phase period.
For 0 <= t <= 4*quarterTime the replacement duration is nonnegative. -/
theorem inverse_forward {n : Type*} [Fintype n] [DecidableEq n]
    (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.phase e p (-t) =
      RootTransferPhase.phase e p (4*RootTransferPhase.quarterTime p-t) := by
  let F := RootTransferPhase.phase e p (4*RootTransferPhase.quarterTime p-t)
  let T := RootTransferPhase.phase e p t
  have hprod : F*T = 1 := by
    rw [← phase_add]
    rw [show 4*RootTransferPhase.quarterTime p-t+t =
      4*RootTransferPhase.quarterTime p by ring, four_quarter_return e he p hp hp1]
  have hu : T*Tᴴ = 1 := (RootTransferPhase.phase_unitary e he p t).2
  have hF : F = Tᴴ := by
    calc
      F = F*(T*Tᴴ) := by rw [hu, Matrix.mul_one]
      _ = (F*T)*Tᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = Tᴴ := by rw [hprod, Matrix.one_mul]
  exact (hF.trans (phase_adjoint e he p t)).symm

lemma forward_duration_nonneg (p t : ℝ) (ht : t ≤ 4*RootTransferPhase.quarterTime p) :
    0 ≤ 4*RootTransferPhase.quarterTime p-t := sub_nonneg.mpr ht

theorem conjugator_inverse_program (c : Fin 3) (p : ℝ) : (conjugator c p)ᴴ =
    RootTransferPhase.phase (rootEvent c 2 3) p (RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c 2 2) p (RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c 0 1) p (-RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c 0 0) p (-RootTransferPhase.quarterTime p) := by
  simp only [conjugator, conjTranspose_mul, phase_adjoint _ (root_twice _ _ _),
    neg_neg, Matrix.mul_assoc]

lemma S_unitary : S ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [S, conjTranspose_apply, mul_apply, Fin.sum_univ_four]

lemma S_conjugates : S * B 1 * Sᴴ = -ConcreteFermion.beta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S, B, BZ, ConcreteFermion.beta, conjTranspose_apply, mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

/-- A unitary change of the native frame can disturb hidden modes temporarily;
its inverse restores them around a completed operation. -/
theorem conjugate_completion {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (E : Matrix a b ℂ)
    (Q : Matrix a a ℂ) (T U : Matrix b b ℂ)
    (ho : NativeObservation.Obs E Q T) (hu : Q ∈ unitary (Matrix a a ℂ)) :
    Q * IsometricDynamics.extend E U * Qᴴ = IsometricDynamics.extend E (T*U*Tᴴ) := by
  have hstar : Eᴴ * Qᴴ = Tᴴ * Eᴴ := by
    simpa only [conjTranspose_mul] using congrArg conjTranspose ho.1
  have hP : Q * IsometricDynamics.complement E = IsometricDynamics.complement E * Q := by
    simp only [IsometricDynamics.complement, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul,
      NativeObservation.commutes ho]
  have hmain : Q*(E*U*Eᴴ)*Qᴴ = E*(T*U*Tᴴ)*Eᴴ := by
    calc
      _ = (Q*E)*U*(Eᴴ*Qᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ho.1,hstar]; simp only [Matrix.mul_assoc]
  have hQQ : Q*Qᴴ = 1 := hu.2
  have heven : Q*IsometricDynamics.complement E*Qᴴ = IsometricDynamics.complement E := by
    rw [hP, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  simp only [IsometricDynamics.extend, Matrix.mul_add, Matrix.add_mul]
  rw [hmain,heven]

lemma conjugated_exponential (p t : ℝ) :
    S * NormedSpace.exp ((Complex.I * ((RootTransferPhase.gap p*(-t) : ℝ) : ℂ)) • B 1) * Sᴴ =
      NormedSpace.exp ((Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • ConcreteFermion.beta) := by
  let U : unitary (Matrix (Fin 4) (Fin 4) ℂ) := ⟨S,S_unitary⟩
  have he := Matrix.exp_units_conj (Unitary.toUnits U)
    ((Complex.I * ((RootTransferPhase.gap p*(-t) : ℝ) : ℂ)) • B 1)
  change NormedSpace.exp (S *
    ((Complex.I * ((RootTransferPhase.gap p*(-t) : ℝ) : ℂ)) • B 1) * Sᴴ) = _ at he
  rw [Matrix.mul_smul, Matrix.smul_mul, S_conjugates] at he
  have hs : (Complex.I * ((RootTransferPhase.gap p*(-t) : ℝ) : ℂ)) • (-ConcreteFermion.beta) =
      (Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • ConcreteFermion.beta := by
    simp
  rw [hs] at he
  exact he.symm

/-- Scheduled root pulses and their inverse conjugation, with no auxiliary carrier bank. -/
def flipPulse (c : Fin 3) (p t : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  if c = 1 then conjugator c p * blockPulse c p (-t) * (conjugator c p)ᴴ
  else blockPulse c p t

/-- Every carrier class admits this exact identity-completed coherent beta pulse
within the stated family of root phases and inverse controls. -/
theorem flip_completed (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    flipPulse c p t = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation ConcreteFermion.beta (RootTransferPhase.gap p*t)) := by
  by_cases hc : c = 1
  · subst c
    simp only [flipPulse, ite_true]
    rw [block_completed,
      conjugate_completion _ _ _ _ (conjugator_observed 1 p hp hp1) (conjugator_unitary 1 p),
      conjugated_exponential, NativeObservation.exp_involution _ ConcreteFermion.beta_square]
  · simp only [flipPulse, hc, ite_false]
    rw [block_completed]
    have hb : B c = ConcreteFermion.beta := by
      change (fun i j => (BZ c i j : ℂ)) = ConcreteFermion.beta
      unfold BZ
      simp only [hc, ite_false]
      exact CarrierWeyl.beta_eq
    rw [hb, NativeObservation.exp_involution _ ConcreteFermion.beta_square]

/-- Every even record mode is restored at the end of the complete pulse. -/
theorem flip_fixes_even (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    flipPulse c p t * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  rw [flip_completed c p t hp hp1]
  simp only [IsometricDynamics.extend, Matrix.add_mul, Matrix.mul_assoc,
    IsometricDynamics.complement_right _ (isometry c), Matrix.mul_zero, zero_add,
    IsometricDynamics.complement_square _ (isometry c)]

/-- Complete coherent pulse unitarity, including its unchanged even sector. -/
theorem flip_unitary (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    flipPulse c p t ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  rw [flip_completed c p t hp hp1]
  exact IsometricDynamics.unitary _ (isometry c) _
    (LocalUnitary.rotation_unitary _ _ ConcreteFermion.beta_hermitian ConcreteFermion.beta_square)

theorem flip_intertwines (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    flipPulse c p t * embedding c =
      embedding c * LocalUnitary.rotation ConcreteFermion.beta (RootTransferPhase.gap p*t) := by
  rw [flip_completed c p t hp hp1]
  exact IsometricDynamics.intertwining _ (isometry c) _

/-- Every observable supported on the even record sector is preserved by the
complete pulse, without identifying that direct sum with a tensor factor. -/
theorem even_record_readout (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (A : Matrix (Carrier c) (Carrier c) ℂ) :
    (flipPulse c p t)ᴴ *
        (IsometricDynamics.complement (embedding c) * A * IsometricDynamics.complement (embedding c)) *
        flipPulse c p t =
      IsometricDynamics.complement (embedding c) * A * IsometricDynamics.complement (embedding c) := by
  have hl : IsometricDynamics.complement (embedding c) * flipPulse c p t =
      IsometricDynamics.complement (embedding c) := by
    rw [flip_completed c p t hp hp1]
    simp only [IsometricDynamics.extend, Matrix.mul_add, ← Matrix.mul_assoc,
      IsometricDynamics.complement_left _ (isometry c), Matrix.zero_mul, zero_add,
      IsometricDynamics.complement_square _ (isometry c)]
  have hs : (flipPulse c p t)ᴴ * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
    have h := congrArg conjTranspose hl
    simpa only [conjTranspose_mul, IsometricDynamics.complement, conjTranspose_sub,
      conjTranspose_one, conjTranspose_conjTranspose] using h
  calc
    _ = ((flipPulse c p t)ᴴ * IsometricDynamics.complement (embedding c)) * A *
        (IsometricDynamics.complement (embedding c) * flipPulse c p t) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs,hl]

end PMAction.PairedRootFlip
