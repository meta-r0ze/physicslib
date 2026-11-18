import PMAction.PairedRootFlip
import PMAction.SpinorEvenFrame
import PMAction.EvenRootPhase
import PMSubstrate.E8Values

/-!
# A common root echo for all carrier classes

A fixed signed root block has the desired beta action in every odd sector,
but can move the even spinor modes. The existing common odd i phase reverses
that unwanted generator without reversing beta. Refocusing retains, uses and
then restores the phase circuit's even action; it does not assume that action
is trivial. The program never queries the glue class. Common root rates,
coherent phase admission, primitive prices and physical timing remain inputs.
-/
noncomputable section
namespace PMAction.ClassBlindFlip
open Matrix CarrierEvents CarrierParity PairedRootFlip
open scoped Matrix.Norms.Operator

def signs : Fin 4 → ℤ := ![1,-1,1,-1]
def T (c : Fin 3) : Matrix (Carrier c) (Carrier c) ℂ :=
  (1/2 : ℂ) • (∑ j : Fin 4, (signs j : ℂ) • (rootEvent c 1 j).permMatrix ℂ)
def compressed (c : Fin 3) := embedding c * ConcreteFermion.beta * (embedding c)ᴴ

def edges : Bool → Fin 4 → Fin 4 × Fin 4
  | false => ![(2,3),(0,1),(2,3),(0,1)]
  | true => ![(1,3),(0,2),(1,3),(0,2)]
def pairMap (a : Bool) (j : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.swap (edges a j).1 (edges a j).2
def J (a : Bool) (j : Fin 4) := (pairMap a j).permMatrix ℂ

theorem even_certificate : ∀ a j (v : Carrier 1) k,
    SpinorEvenFrame.indicator (rootEvent 1 (if a then 1 else 0) j v) k =
      SpinorEvenFrame.indicator v (pairMap a j k) := by decide +kernel

lemma even_intertwines (a : Bool) (j : Fin 4) :
    (rootEvent 1 (if a then 1 else 0) j).permMatrix ℂ * SpinorEvenFrame.embedding =
      SpinorEvenFrame.embedding * J a j := by
  ext v k
  change (_ *ᵥ fun w => SpinorEvenFrame.embedding w k) v =
    (SpinorEvenFrame.embedding v ᵥ* (pairMap a j).permMatrix ℂ) k
  rw [permMatrix_mulVec, vecMul_permMatrix]
  change VectorEvenFrame.scale * (SpinorEvenFrame.indicator (rootEvent 1 (if a then 1 else 0) j v) k : ℂ) = _
  rw [even_certificate]
  simp only [SpinorEvenFrame.embedding, pairMap, Equiv.symm_swap, Function.comp_apply]

lemma even_observed (a : Bool) (j : Fin 4) :
    NativeObservation.Obs SpinorEvenFrame.embedding
      ((rootEvent 1 (if a then 1 else 0) j).permMatrix ℂ) (J a j) := by
  refine ⟨even_intertwines a j, ?_⟩
  have h := congrArg conjTranspose (even_intertwines a j)
  have hJ : (J a j)ᴴ = J a j :=
    (RootTransferPhase.permutation_hermitian _ (by intro x; simp [pairMap])).eq
  simpa [conjTranspose_mul, (RootTransferPhase.permutation_hermitian _
    (root_twice 1 (if a then 1 else 0) j)).eq, hJ] using h

def evenFactor (a : Bool) (j : Fin 4) (z : ℂ) :=
  InvolutionSpectral.plus (J a j) + z • InvolutionSpectral.minus (J a j)

lemma even_phase (a : Bool) (j : Fin 4) (p t : ℝ) :
    NativeObservation.Obs SpinorEvenFrame.embedding
      (RootTransferPhase.phase (rootEvent 1 (if a then 1 else 0) j) p t)
      (evenFactor a j (Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I))) := by
  rw [RootTransferPhase.phase_formula _ (root_twice 1 _ j)]
  exact NativeObservation.add
    (NativeObservation.smul (1/2 : ℂ)
      (NativeObservation.add NativeObservation.one (even_observed a j)))
    (NativeObservation.smul _ (NativeObservation.smul (1/2 : ℂ)
      (NativeObservation.sub NativeObservation.one (even_observed a j))))

lemma base_event : ∀ c j, rootEvent c 0 j = OrthogonalRootPhase.event c j := by
  intro c j
  apply Equiv.ext
  intro v
  revert c j v
  decide +kernel

def H := (1/2 : ℂ) • (∑ j : Fin 4, (signs j : ℂ) • J true j)
def K := J false 0 * J false 1

lemma T_even : NativeObservation.Obs SpinorEvenFrame.embedding (T 1) H := by
  unfold T H
  simp only [Fin.sum_univ_four]
  exact NativeObservation.smul _ (NativeObservation.add
    (NativeObservation.add (NativeObservation.add
      (NativeObservation.smul _ (even_observed true 0))
      (NativeObservation.smul _ (even_observed true 1)))
      (NativeObservation.smul _ (even_observed true 2)))
      (NativeObservation.smul _ (even_observed true 3)))

set_option maxHeartbeats 1000000 in
lemma phase_even_matrix :
    evenFactor false 0 Complex.I * evenFactor false 1 Complex.I *
      evenFactor false 2 Complex.I * evenFactor false 3 Complex.I = K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenFactor, InvolutionSpectral.plus, InvolutionSpectral.minus,
      J, pairMap, edges, K, Equiv.swap_apply_def, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, mul_apply, Fin.sum_univ_four]
  all_goals ring_nf
  all_goals norm_num

lemma phase_even (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs SpinorEvenFrame.embedding (OddCarrierPhase.phaseI 1 p) K := by
  have h (j : Fin 4) := even_phase false j p (3*RootTransferPhase.quarterTime p)
  simp only [Bool.false_eq_true, ↓reduceIte, base_event,
    EvenRootPhase.phaseI_coefficient 1 p hp hp1] at h
  simpa only [OddCarrierPhase.phaseI, OrthogonalRootPhase.phase, phase_even_matrix] using
    NativeObservation.mul (NativeObservation.mul (NativeObservation.mul (h 0) (h 1)) (h 2)) (h 3)

lemma phase_odd (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs (embedding c) (OddCarrierPhase.phaseI c p)
      (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
  apply NativeSector.obs_of c
  · simpa using OddCarrierPhase.phaseI_sector c p hp hp1
  · exact NativeSector.phaseI_commute c p

set_option maxHeartbeats 1000000 in
lemma T_odd (c : Fin 3) : NativeObservation.Obs (embedding c) (T c) ConcreteFermion.beta := by
  have h := NativeObservation.smul (1/2 : ℂ) (NativeObservation.add
    (NativeObservation.add (NativeObservation.add
      (NativeObservation.smul (signs 0 : ℂ) (root_observed c 1 0))
      (NativeObservation.smul (signs 1 : ℂ) (root_observed c 1 1)))
      (NativeObservation.smul (signs 2 : ℂ) (root_observed c 1 2)))
      (NativeObservation.smul (signs 3 : ℂ) (root_observed c 1 3)))
  have he : (1/2 : ℂ) • ((signs 0 : ℂ) • R 1 0 + (signs 1 : ℂ) • R 1 1 +
      (signs 2 : ℂ) • R 1 2 + (signs 3 : ℂ) • R 1 3) = ConcreteFermion.beta := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signs, R, RZ, axisPerm, OrthogonalRootPhase.realMatrix, ConcreteFermion.beta, Equiv.swap_apply_def]
  simpa only [T, Fin.sum_univ_four, he] using h

set_option maxHeartbeats 1000000 in
lemma even_reversed : K * H * Kᴴ = -H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, H, signs, J, pairMap, edges, Equiv.swap_apply_def, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, mul_apply, Fin.sum_univ_four, conjTranspose_apply]

lemma phase_unitary (c : Fin 3) (p : ℝ) :
    OddCarrierPhase.phaseI c p ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  unfold OddCarrierPhase.phaseI OrthogonalRootPhase.phase
  exact mul_mem (mul_mem (mul_mem
    (RootTransferPhase.phase_unitary _ (OrthogonalRootPhase.event_involutive c 0) _ _)
    (RootTransferPhase.phase_unitary _ (OrthogonalRootPhase.event_involutive c 1) _ _))
    (RootTransferPhase.phase_unitary _ (OrthogonalRootPhase.event_involutive c 2) _ _))
    (RootTransferPhase.phase_unitary _ (OrthogonalRootPhase.event_involutive c 3) _ _)

lemma compressed_invariant (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    OddCarrierPhase.phaseI c p * compressed c * (OddCarrierPhase.phaseI c p)ᴴ = compressed c := by
  have ho := phase_odd c p hp hp1
  calc
    _ = (OddCarrierPhase.phaseI c p * embedding c) * ConcreteFermion.beta *
      ((embedding c)ᴴ * (OddCarrierPhase.phaseI c p)ᴴ) := by
        simp only [compressed, Matrix.mul_assoc]
    _ = _ := by
      rw [ho.1, (NativeObservation.star ho).2]
      simp [compressed, Matrix.mul_smul, Matrix.smul_mul, smul_smul]

lemma T_other (c : Fin 3) (hc : c ≠ 1) : T c = compressed c := by
  have hg := generator_compressed c
  rw [generator_roots] at hg
  have hs : sign c = signs := by simp [sign, signs, hc]
  have hb : B c = ConcreteFermion.beta := by
    change (fun i j => (BZ c i j : ℂ)) = ConcreteFermion.beta
    unfold BZ
    simp only [hc, ite_false]
    exact CarrierWeyl.beta_eq
  simpa only [hs, hb, T, compressed] using hg

/-- Exact full-label refocusing, including all even modes. -/
theorem echo_generator (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    T c + OddCarrierPhase.phaseI c p * T c * (OddCarrierPhase.phaseI c p)ᴴ =
      (2 : ℂ) • compressed c := by
  by_cases hc : c = 1
  · subst c
    apply SpinorEvenFrame.eq_of_frames
    · have hQ := phase_odd 1 p hp hp1
      have h := NativeObservation.add (T_odd 1)
        (NativeObservation.mul (NativeObservation.mul hQ (T_odd 1)) (NativeObservation.star hQ))
      have hs : ConcreteFermion.beta + (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) *
          ConcreteFermion.beta * (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ))ᴴ =
          (2 : ℂ) • ConcreteFermion.beta := by
        simp [smul_smul, two_smul]
      rw [hs] at h
      rw [h.1]
      simp [compressed, Matrix.mul_assoc, isometry, Matrix.smul_mul, Matrix.mul_smul]
    · have hQ := phase_even p hp hp1
      have h := NativeObservation.add T_even
        (NativeObservation.mul (NativeObservation.mul hQ T_even) (NativeObservation.star hQ))
      rw [even_reversed, add_neg_cancel] at h
      rw [h.1]
      simp only [Matrix.mul_zero, compressed, Matrix.smul_mul, Matrix.mul_assoc,
        SpinorEvenFrame.odd_orthogonal, Matrix.mul_zero, smul_zero]
  · rw [T_other c hc, compressed_invariant c p hp hp1, two_smul]

lemma T_commutes_compressed (c : Fin 3) : Commute (T c) (compressed c) := by
  have h := T_odd c
  show _ * _ = _ * _
  calc
    _ = (T c * embedding c) * ConcreteFermion.beta * (embedding c)ᴴ := by
      simp only [compressed, Matrix.mul_assoc]
    _ = embedding c * ConcreteFermion.beta * ((embedding c)ᴴ * T c) := by
      rw [h.1, h.2]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [compressed, Matrix.mul_assoc]

lemma echo_commutes (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    Commute (T c) (OddCarrierPhase.phaseI c p * T c * (OddCarrierPhase.phaseI c p)ᴴ) := by
  have he : OddCarrierPhase.phaseI c p * T c * (OddCarrierPhase.phaseI c p)ᴴ =
      (2 : ℂ) • compressed c - T c := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using echo_generator c p hp hp1
  rw [he]
  exact ((T_commutes_compressed c).smul_right (2 : ℂ)).sub_right (Commute.refl _)

/-- The same four signed primitive pulses in every glue class. -/
def block (c : Fin 3) (p t : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  RootTransferPhase.phase (rootEvent c 1 0) p t *
    RootTransferPhase.phase (rootEvent c 1 1) p (-t) *
    RootTransferPhase.phase (rootEvent c 1 2) p t *
    RootTransferPhase.phase (rootEvent c 1 3) p (-t)

def exponent (c : Fin 3) (p t : ℝ) (j : Fin 4) :=
  (((-((signs j : ℝ)*t) : ℝ) : ℂ) * Complex.I) •
    RootTransferPhase.generator (rootEvent c 1 j) p

set_option maxHeartbeats 1000000 in
lemma block_exponential (c : Fin 3) (p t : ℝ) : block c p t =
    NormedSpace.exp ((Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • T c) := by
  have hcomm : ∀ i j, Commute (exponent c p t i) (exponent c p t j) := by
    intro i j
    show _ * _ = _ * _
    simp only [exponent, smul_mul_smul_comm]
    rw [(generator_commutes c p i j).eq, mul_comm]
  have hs : exponent c p t 0 + exponent c p t 1 + exponent c p t 2 + exponent c p t 3 =
      (Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • T c := by
    simp only [exponent, T, RootTransferPhase.generator, InvolutionSpectral.minus,
      Fin.sum_univ_four]
    norm_num [signs, smul_sub, smul_smul]
    module
  rw [← hs, PairedRootFlip.exp_four _ hcomm]
  simp only [exponent, signs]
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, neg_neg]
  simp only [block, RootTransferPhase.phase, neg_neg]

/-- Multiplication order is explicit; no physical class controller occurs in this definition. -/
def pulse (c : Fin 3) (p t : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  block c p (t/2) * OddCarrierPhase.phaseI c p * block c p (t/2) *
    (OddCarrierPhase.phaseI c p)ᴴ

/-- The refocusing is exact, rather than a small-time product approximation. -/
theorem pulse_exponential (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    pulse c p t = NormedSpace.exp
      ((Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • compressed c) := by
  let z : ℂ := Complex.I * ((RootTransferPhase.gap p*(t/2) : ℝ) : ℂ)
  let Q := OddCarrierPhase.phaseI c p
  let U : unitary (Matrix (Carrier c) (Carrier c) ℂ) := ⟨Q,phase_unitary c p⟩
  have he := Matrix.exp_units_conj (Unitary.toUnits U) (z • T c)
  change NormedSpace.exp (Q * (z • T c) * Qᴴ) =
    Q * NormedSpace.exp (z • T c) * Qᴴ at he
  have hc : Commute (z • T c) (z • (Q * T c * Qᴴ)) :=
    (echo_commutes c p hp hp1).smul_left z |>.smul_right z
  have hs : z • T c + z • (Q * T c * Qᴴ) =
      (Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)) • compressed c := by
    rw [← smul_add, echo_generator c p hp hp1, smul_smul]
    congr 1
    dsimp [z]
    push_cast
    ring
  unfold pulse
  rw [block_exponential]
  change NormedSpace.exp (z • T c) * Q * NormedSpace.exp (z • T c) * Qᴴ = _
  calc
    _ = NormedSpace.exp (z • T c) * (Q * NormedSpace.exp (z • T c) * Qᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = NormedSpace.exp (z • T c) * NormedSpace.exp (z • (Q * T c * Qᴴ)) := by
      rw [← he, Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [← Matrix.exp_add_of_commute _ _ hc, hs]

/-- One common root program completes beta by identity on all invisible modes. -/
theorem pulse_completed (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    pulse c p t = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation ConcreteFermion.beta (RootTransferPhase.gap p*t)) := by
  let z : ℂ := Complex.I * ((RootTransferPhase.gap p*t : ℝ) : ℂ)
  have hg : compressed c * embedding c = embedding c * ConcreteFermion.beta := by
    simp [compressed, Matrix.mul_assoc, isometry]
  have hP : compressed c * IsometricDynamics.complement (embedding c) = 0 := by
    rw [compressed, Matrix.mul_assoc, IsometricDynamics.complement_right _ (isometry c),
      Matrix.mul_zero]
  have hA : pulse c p t * embedding c = embedding c * NormedSpace.exp (z • ConcreteFermion.beta) := by
    rw [pulse_exponential c p t hp hp1]
    exact RectangularEvolution.scaled _ _ _ hg z
  have hc : pulse c p t = IsometricDynamics.extend (embedding c)
      (NormedSpace.exp (z • ConcreteFermion.beta)) := by
    apply (CompletionSelection.agreement_iff _ (isometry c) _ _ hA).mpr
    rw [pulse_exponential c p t hp hp1]
    have he := RectangularEvolution.scaled (compressed c) 0
      (IsometricDynamics.complement (embedding c)) (by simpa using hP) z
    simpa [z] using he
  rw [hc]
  congr 1
  exact NativeObservation.exp_involution _ ConcreteFermion.beta_square _

theorem pulse_unitary (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    pulse c p t ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  rw [pulse_completed c p t hp hp1]
  exact IsometricDynamics.unitary _ (isometry c) _
    (LocalUnitary.rotation_unitary _ _ ConcreteFermion.beta_hermitian ConcreteFermion.beta_square)

theorem pulse_fixes_even (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    pulse c p t * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  rw [pulse_completed c p t hp hp1]
  simp only [IsometricDynamics.extend, Matrix.add_mul, Matrix.mul_assoc,
    IsometricDynamics.complement_right _ (isometry c), Matrix.mul_zero, zero_add,
    IsometricDynamics.complement_square _ (isometry c)]

/-- A forward-parameter realization of the fixed signed block. -/
def forwardBlock (c : Fin 3) (p t : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  RootTransferPhase.phase (rootEvent c 1 0) p t *
    RootTransferPhase.phase (rootEvent c 1 1) p (4*RootTransferPhase.quarterTime p-t) *
    RootTransferPhase.phase (rootEvent c 1 2) p t *
    RootTransferPhase.phase (rootEvent c 1 3) p (4*RootTransferPhase.quarterTime p-t)

lemma forwardBlock_eq (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    forwardBlock c p t = block c p t := by
  unfold forwardBlock block
  rw [inverse_forward _ (root_twice c 1 1) p t hp hp1,
    inverse_forward _ (root_twice c 1 3) p t hp hp1]

/-- The echo's inverse consists of four reversed base-root pulses at positive quarter-time. -/
lemma phase_inverse_program (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    (OddCarrierPhase.phaseI c p)ᴴ =
      RootTransferPhase.phase (OrthogonalRootPhase.event c 3) p (RootTransferPhase.quarterTime p) *
      RootTransferPhase.phase (OrthogonalRootPhase.event c 2) p (RootTransferPhase.quarterTime p) *
      RootTransferPhase.phase (OrthogonalRootPhase.event c 1) p (RootTransferPhase.quarterTime p) *
      RootTransferPhase.phase (OrthogonalRootPhase.event c 0) p (RootTransferPhase.quarterTime p) := by
  have h (j : Fin 4) :
      RootTransferPhase.phase (OrthogonalRootPhase.event c j) p (- (3*RootTransferPhase.quarterTime p)) =
      RootTransferPhase.phase (OrthogonalRootPhase.event c j) p (RootTransferPhase.quarterTime p) := by
    rw [inverse_forward _ (OrthogonalRootPhase.event_involutive c j) _ _ hp hp1]
    congr 1
    ring
  simp only [OddCarrierPhase.phaseI, OrthogonalRootPhase.phase, conjTranspose_mul,
    phase_adjoint _ (OrthogonalRootPhase.event_involutive _ _), h, Matrix.mul_assoc]

/-- A fixed sixteen-root implementation with no negative parameter on the stated interval. -/
def forwardPulse (c : Fin 3) (p t : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  forwardBlock c p (t/2) * OddCarrierPhase.phaseI c p * forwardBlock c p (t/2) *
    (RootTransferPhase.phase (OrthogonalRootPhase.event c 3) p (RootTransferPhase.quarterTime p) *
      RootTransferPhase.phase (OrthogonalRootPhase.event c 2) p (RootTransferPhase.quarterTime p) *
      RootTransferPhase.phase (OrthogonalRootPhase.event c 1) p (RootTransferPhase.quarterTime p) *
      RootTransferPhase.phase (OrthogonalRootPhase.event c 0) p (RootTransferPhase.quarterTime p))

theorem forwardPulse_eq (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    forwardPulse c p t = pulse c p t := by
  unfold forwardPulse pulse
  rw [forwardBlock_eq c p (t/2) hp hp1, phase_inverse_program c p hp hp1]

/-- Serial parameter ledger: two signed blocks, the common phase, and its inverse.
This counts the literal sixteen pulses above, not an optimal duration or hop-time calibration. -/
def forwardTimes (p t : ℝ) : Fin 16 → ℝ :=
  let q := RootTransferPhase.quarterTime p
  ![t/2,4*q-t/2,t/2,4*q-t/2, 3*q,3*q,3*q,3*q,
    t/2,4*q-t/2,t/2,4*q-t/2, q,q,q,q]

theorem forwardTimes_nonnegative (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (ht : 0 ≤ t) (ht1 : t ≤ 8*RootTransferPhase.quarterTime p) :
    ∀ j, 0 ≤ forwardTimes p t j := by
  have hq := RootTransferPhase.quarterTime_positive p hp hp1
  intro j
  fin_cases j <;> norm_num [forwardTimes, Matrix.cons_val] <;> linarith

/-- Fixed forward-return overhead is visible; the output-angle parameter t is not elapsed time. -/
theorem forwardTimes_total (p t : ℝ) :
    (∑ j, forwardTimes p t j) = 32*RootTransferPhase.quarterTime p := by
  norm_num [forwardTimes, Fin.sum_univ_succ]
  ring

/-- Each of the sixteen forward pulse durations is a whole substrate tick count. -/
def TickAligned (p t : ℝ) : Prop :=
  ∀ j, ∃ k : ℕ, forwardTimes p t j = (k : ℝ)

/-- A certain beta flip makes the quarter-time an even number of substrate
ticks. A quarter-time and the half-angle parameter both occur as actual pulse
durations in this particular forward program. -/
theorem certain_quarter_even {p t : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ha : TickAligned p t) (hfull : Real.cos (RootTransferPhase.gap p * t) = 0) :
    ∃ m : ℕ, 0 < m ∧ RootTransferPhase.quarterTime p = (2 * m : ℕ) := by
  obtain ⟨q, hq⟩ := ha 12
  obtain ⟨n, hn⟩ := ha 0
  norm_num [forwardTimes, Matrix.cons_val] at hq hn
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hfull
  have ht : t = (2 * (k : ℝ) + 1) * RootTransferPhase.quarterTime p := by
    apply mul_left_cancel₀ (RootTransferPhase.gap_positive p hp hp1).ne'
    rw [hk, mul_left_comm, quarter_angle p hp hp1]
    ring
  have hreal : (2 : ℝ) * n = (2 * (k : ℝ) + 1) * q := by
    rw [← hq, ← hn, ht]
    ring
  have hint : (2 : ℤ) * n = (2 * k + 1) * q := by exact_mod_cast hreal
  have hparity : (2 : ℤ) * n = 2 * (k * q) + q := hint.trans (by ring)
  have hqpos : 0 < q := by
    exact_mod_cast hq ▸ RootTransferPhase.quarterTime_positive p hp hp1
  refine ⟨q / 2, by omega, ?_⟩
  have he : q = 2 * (q / 2) := by omega
  exact hq.trans (by exact_mod_cast he)

/-- A full tick-aligned execution of the checked echo takes at least 64
ticks, so it cannot occur once in a 43-tick serial frame. -/
theorem certain_tick_duration_lower {p t : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ha : TickAligned p t) (hfull : Real.cos (RootTransferPhase.gap p * t) = 0) :
    64 ≤ ∑ j, forwardTimes p t j := by
  obtain ⟨m, hm, hq⟩ := certain_quarter_even hp hp1 ha hfull
  rw [forwardTimes_total, hq]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  linarith

/-- A complete tick-aligned flip using this program cannot fit the substrate
period. This conclusion already holds before allocating any crossing pulses. -/
theorem certain_does_not_fit_e8_frame {p t : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ha : TickAligned p t) (hfull : Real.cos (RootTransferPhase.gap p * t) = 0) :
    (PMSubstrate.E8Values.Delta : ℝ) < ∑ j, forwardTimes p t j := by
  exact lt_of_lt_of_le (by norm_num [show PMSubstrate.E8Values.Delta = 43 from rfl])
    (certain_tick_duration_lower hp hp1 ha hfull)

/-- Six serial half-pulse reflections on that same clock use at least 24 ticks
in addition to the certain flip's 64. This is the time budget when a crossing is
implemented as a serial six-reflection word. -/
theorem certain_with_six_reflections_lower {p t : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ha : TickAligned p t) (hfull : Real.cos (RootTransferPhase.gap p * t) = 0) :
    88 ≤ (∑ j, forwardTimes p t j) + 6 * (2 * RootTransferPhase.quarterTime p) := by
  obtain ⟨m, hm, hq⟩ := certain_quarter_even hp hp1 ha hfull
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [forwardTimes_total, hq]
  push_cast
  linarith

/-- The 64-tick lower bound is attained by the same native program, with
principal beta angle pi/2 and one whole tick in each short pulse. -/
theorem certain_tick_duration_attained :
    ∃ p : ℝ, 0 < p ∧ p < 1/2 ∧ RootTransferPhase.quarterTime p = 2 ∧
      TickAligned p 2 ∧
      RootTransferPhase.gap p * 2 = Real.pi / 2 ∧
      (∑ j, forwardTimes p 2 j) = 64 ∧
      ∀ c, forwardPulse c p 2 = IsometricDynamics.extend (embedding c)
        (Complex.I • ConcreteFermion.beta) := by
  let p := (1 - Real.exp (-Real.pi / 8)) / 2
  have hp : 0 < p := by
    have he := Real.exp_lt_one_iff.mpr (show -Real.pi / 8 < 0 by
      linarith [Real.pi_pos])
    dsimp [p]
    linarith
  have hp1 : p < 1 / 2 := by
    dsimp [p]
    linarith [Real.exp_pos (-Real.pi / 8)]
  have hr : RootTransferPhase.residual p = Real.exp (-Real.pi / 8) := by
    dsimp [RootTransferPhase.residual,p]
    ring
  have hg : RootTransferPhase.gap p = Real.pi / 4 := by
    rw [RootTransferPhase.gap, hr, Real.log_exp]
    ring
  have hq : RootTransferPhase.quarterTime p = 2 := by
    rw [RootTransferPhase.quarterTime, hg]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hangle : RootTransferPhase.gap p * 2 = Real.pi / 2 := by rw [hg]; ring
  refine ⟨p, hp, hp1, hq, ?_, hangle, by rw [forwardTimes_total, hq]; norm_num, ?_⟩
  · intro j
    refine ⟨(![1,7,1,7,6,6,6,6,1,7,1,7,2,2,2,2] : Fin 16 → ℕ) j, ?_⟩
    fin_cases j <;> norm_num [forwardTimes, hq, Matrix.cons_val]
  · intro c
    rw [forwardPulse_eq c p 2 hp hp1, pulse_completed c p 2 hp hp1, hangle]
    simp [LocalUnitary.rotation]

/-- On the same calibrated clock, a further full rotation can be hidden
inside the very same serial duration and completed coherent action. Selecting
the principal rotation needs information beyond the endpoint and total time. -/
theorem full_turn_same_time_and_readout {p : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (hq : RootTransferPhase.quarterTime p = 2) :
    TickAligned p 10 ∧
      RootTransferPhase.gap p * 10 = 5 * (Real.pi / 2) ∧
      (∑ j, forwardTimes p 10 j) = (∑ j, forwardTimes p 2 j) ∧
      ∀ c, forwardPulse c p 10 = forwardPulse c p 2 := by
  have h2 : RootTransferPhase.gap p * 2 = Real.pi / 2 := by
    simpa only [hq] using quarter_angle p hp hp1
  have h10 : RootTransferPhase.gap p * 10 = Real.pi / 2 + 2 * Real.pi := by linarith
  refine ⟨?_, by linarith, by rw [forwardTimes_total, forwardTimes_total], ?_⟩
  · intro j
    refine ⟨(![5,3,5,3,6,6,6,6,5,3,5,3,2,2,2,2] : Fin 16 → ℕ) j, ?_⟩
    fin_cases j <;> norm_num [forwardTimes, hq, Matrix.cons_val]
  · intro c
    rw [forwardPulse_eq c p 10 hp hp1, forwardPulse_eq c p 2 hp hp1,
      pulse_completed c p 10 hp hp1, pulse_completed c p 2 hp hp1, h10, h2]
    simp [LocalUnitary.rotation]

end PMAction.ClassBlindFlip
