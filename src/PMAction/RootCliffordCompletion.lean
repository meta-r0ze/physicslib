import PMAction.ClassBlindFlip

/-!
# Completed internal Clifford rotations from the common root echo

The beta echo can be conjugated by actual primitive-root phases to rotate
chirality and each spatial internal generator. Every program is independent
of the glue class; direction indices select fixed spatial axes. The proof uses
the phase gates' full even action and restores it by inverse conjugation.

This constructs internal controls under the existing common-rate and coherent
phase-admission contract. It does not select the native event, price the larger
circuits, calibrate hop time, or supply site-conditioned transport and the
inter-wall crossing. No composite permutation is assigned a lazy generator.
-/
noncomputable section
namespace PMAction.RootCliffordCompletion
open Matrix CarrierEvents CarrierParity PairedRootFlip
open scoped Matrix.Norms.Operator

/-- Two actual orthogonal-root phases, each at the existing positive i-phase time. -/
def pairPulse (c : Fin 3) (p : ℝ) (a : Fin 3) (j k : Fin 4) :=
  RootTransferPhase.phase (rootEvent c a j) p (3*RootTransferPhase.quarterTime p) *
    RootTransferPhase.phase (rootEvent c a k) p (3*RootTransferPhase.quarterTime p)
def pairCoordinate (a : Fin 3) (j k : Fin 4) := factor a j Complex.I * factor a k Complex.I

lemma pair_observed (c : Fin 3) (p : ℝ) (a : Fin 3) (j k : Fin 4)
    (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs (embedding c) (pairPulse c p a j k) (pairCoordinate a j k) := by
  have h (n : Fin 4) := root_phase_observed c a n p (3*RootTransferPhase.quarterTime p)
  rw [EvenRootPhase.phaseI_coefficient c p hp hp1] at h
  exact NativeObservation.mul (h j) (h k)

lemma pair_unitary (c : Fin 3) (p : ℝ) (a : Fin 3) (j k : Fin 4) :
    pairPulse c p a j k ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) :=
  mul_mem (RootTransferPhase.phase_unitary _ (root_twice c a j) _ _)
    (RootTransferPhase.phase_unitary _ (root_twice c a k) _ _)

/-- A primitive root reflection is a half-period phase, not a new composite event. -/
lemma half_phase (c : Fin 3) (p : ℝ) (a : Fin 3) (j : Fin 4)
    (hp : 0 < p) (hp1 : p < 1/2) :
    RootTransferPhase.phase (rootEvent c a j) p (2*RootTransferPhase.quarterTime p) =
      (rootEvent c a j).permMatrix ℂ :=
  RootTransferPhase.half_pulse _ (root_twice c a j) p hp hp1

def swapPulse (c : Fin 3) (p : ℝ) (a : Fin 3) (j : Fin 4) :=
  RootTransferPhase.phase (rootEvent c a j) p (2*RootTransferPhase.quarterTime p)

lemma swap_observed (c : Fin 3) (p : ℝ) (a : Fin 3) (j : Fin 4)
    (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs (embedding c) (swapPulse c p a j) (R a j) := by
  rw [swapPulse, half_phase c p a j hp hp1]
  exact root_observed c a j

lemma swap_unitary (c : Fin 3) (p : ℝ) (a : Fin 3) (j : Fin 4) :
    swapPulse c p a j ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) :=
  RootTransferPhase.phase_unitary _ (root_twice c a j) _ _

/-- Readout of a full-label unitary on a reducing isometric sector is unitary. -/
lemma observed_unitary {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (E : Matrix a b ℂ) (hE : Eᴴ*E = 1) (Q : Matrix a a ℂ) (S : Matrix b b ℂ)
    (ho : NativeObservation.Obs E Q S) (hu : Q ∈ unitary (Matrix a a ℂ)) :
    S ∈ unitary (Matrix b b ℂ) := by
  have extract {A B : Matrix b b ℂ} (h : E*A = E*B) : A = B := by
    have he := congrArg (fun Z => Eᴴ*Z) h
    simpa only [← Matrix.mul_assoc, hE, Matrix.one_mul] using he
  have hleft : Qᴴ*Q = 1 := hu.1
  have hright : Q*Qᴴ = 1 := hu.2
  constructor
  · change Sᴴ*S = 1
    have h := (NativeObservation.mul (NativeObservation.star ho) ho).1
    rw [hleft, Matrix.one_mul] at h
    exact (extract (by simpa using h)).symm
  · change S*Sᴴ = 1
    have h := (NativeObservation.mul ho (NativeObservation.star ho)).1
    rw [hright, Matrix.one_mul] at h
    exact (extract (by simpa using h)).symm

def gammaCoordinate := pairCoordinate 0 0 1 *
  LocalUnitary.rotation ConcreteFermion.beta (-Real.pi/4) * (pairCoordinate 0 0 1)ᴴ

/-- A fixed quarter-angle beta echo, conjugated by two primitive-root phases. -/
def gammaConjugator (c : Fin 3) (p : ℝ) :=
  pairPulse c p 0 0 1 * ClassBlindFlip.forwardPulse c p (7*RootTransferPhase.quarterTime p/2) *
    (pairPulse c p 0 0 1)ᴴ

lemma gamma_observed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs (embedding c) (gammaConjugator c p) gammaCoordinate := by
  have ht : RootTransferPhase.gap p * (7*RootTransferPhase.quarterTime p/2) = -Real.pi/4 + 2*Real.pi := by
    linarith [quarter_angle p hp hp1]
  have he : NativeObservation.Obs (embedding c)
      (ClassBlindFlip.forwardPulse c p (7*RootTransferPhase.quarterTime p/2))
      (LocalUnitary.rotation ConcreteFermion.beta (-Real.pi/4)) := by
    rw [ClassBlindFlip.forwardPulse_eq c p _ hp hp1, ClassBlindFlip.pulse_completed c p _ hp hp1, ht]
    simp only [LocalUnitary.rotation, Real.cos_add_two_pi, Real.sin_add_two_pi]
    exact ⟨IsometricDynamics.intertwining _ (isometry c) _,
      by simp [IsometricDynamics.extend, Matrix.mul_add, ← Matrix.mul_assoc, isometry,
        IsometricDynamics.complement_right]⟩
  exact NativeObservation.mul (NativeObservation.mul (pair_observed c p 0 0 1 hp hp1) he)
    (NativeObservation.star (pair_observed c p 0 0 1 hp hp1))

lemma gamma_unitary (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    gammaConjugator c p ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) :=
  mul_mem (mul_mem (pair_unitary c p 0 0 1) (by rw [ClassBlindFlip.forwardPulse_eq c p _ hp hp1]; exact ClassBlindFlip.pulse_unitary c p _ hp hp1))
    (Unitary.star_mem (pair_unitary c p 0 0 1))

set_option maxHeartbeats 2000000 in
lemma gamma_conjugates : gammaCoordinate * ConcreteFermion.beta * gammaCoordinateᴴ =
    ConcreteFermion.gamma := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hc : Real.cos (-Real.pi/4) = Real.sqrt 2/2 := by
    simp [neg_div, Real.cos_pi_div_four]
  have hsin : Real.sin (-Real.pi/4) = -(Real.sqrt 2/2) := by
    simp [neg_div, Real.sin_pi_div_four]
  simp only [gammaCoordinate, LocalUnitary.rotation, hc, hsin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairCoordinate, factor, InvolutionSpectral.plus,
      InvolutionSpectral.minus, R, RZ, axisPerm, Equiv.swap_apply_def,
      OrthogonalRootPhase.realMatrix, LocalUnitary.rotation, ConcreteFermion.beta,
      ConcreteFermion.gamma, mul_apply, conjTranspose_apply, Fin.sum_univ_four,
      Real.cos_pi_div_four, Real.sin_pi_div_four, Real.sqrt_div]
  all_goals ring_nf
  all_goals norm_num [hs, Complex.I_sq, map_ofNat]

/-- The imaginary alpha direction uses a two-axis phase, not an assumed odd-only i gate. -/
def alphaCoordinate : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![pairCoordinate 1 0 1 * (pairCoordinate 2 2 3 * R 2 2),
    pairCoordinate 2 2 3 * R 2 2, R 1 2 * gammaCoordinate]

def alphaConjugator (c : Fin 3) (p : ℝ) : Fin 3 → Matrix (Carrier c) (Carrier c) ℂ :=
  ![pairPulse c p 1 0 1 * (pairPulse c p 2 2 3 * swapPulse c p 2 2),
    pairPulse c p 2 2 3 * swapPulse c p 2 2,
    swapPulse c p 1 2 * gammaConjugator c p]

lemma alpha_observed (c : Fin 3) (p : ℝ) (j : Fin 3) (hp : 0 < p) (hp1 : p < 1/2) :
    NativeObservation.Obs (embedding c) (alphaConjugator c p j) (alphaCoordinate j) := by
  fin_cases j
  · exact NativeObservation.mul (pair_observed c p 1 0 1 hp hp1)
      (NativeObservation.mul (pair_observed c p 2 2 3 hp hp1) (swap_observed c p 2 2 hp hp1))
  · exact NativeObservation.mul (pair_observed c p 2 2 3 hp hp1) (swap_observed c p 2 2 hp hp1)
  · exact NativeObservation.mul (swap_observed c p 1 2 hp hp1) (gamma_observed c p hp hp1)

lemma alpha_unitary (c : Fin 3) (p : ℝ) (j : Fin 3) (hp : 0 < p) (hp1 : p < 1/2) :
    alphaConjugator c p j ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  fin_cases j
  · exact mul_mem (pair_unitary c p 1 0 1)
      (mul_mem (pair_unitary c p 2 2 3) (swap_unitary c p 2 2))
  · exact mul_mem (pair_unitary c p 2 2 3) (swap_unitary c p 2 2)
  · exact mul_mem (swap_unitary c p 1 2) (gamma_unitary c p hp hp1)

set_option maxHeartbeats 2000000 in
lemma alpha_conjugates (j : Fin 3) :
    alphaCoordinate j * ConcreteFermion.beta * (alphaCoordinate j)ᴴ = ConcreteFermion.alpha j := by
  fin_cases j
  · ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [alphaCoordinate, pairCoordinate, factor, InvolutionSpectral.plus,
        InvolutionSpectral.minus, R, RZ, axisPerm, Equiv.swap_apply_def,
        OrthogonalRootPhase.realMatrix, ConcreteFermion.beta, ConcreteFermion.alpha,
        mul_apply, conjTranspose_apply, Fin.sum_univ_four]
    all_goals ring_nf
    all_goals norm_num
  · ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [alphaCoordinate, pairCoordinate, factor, InvolutionSpectral.plus,
        InvolutionSpectral.minus, R, RZ, axisPerm, Equiv.swap_apply_def,
        OrthogonalRootPhase.realMatrix, ConcreteFermion.beta, ConcreteFermion.alpha,
        mul_apply, conjTranspose_apply, Fin.sum_univ_four]
    all_goals ring_nf
  · change (R 1 2 * gammaCoordinate) * ConcreteFermion.beta * (R 1 2 * gammaCoordinate)ᴴ = _
    rw [conjTranspose_mul]
    have hr : (R 1 2 * gammaCoordinate) * ConcreteFermion.beta * (gammaCoordinateᴴ * (R 1 2)ᴴ) =
        R 1 2 * (gammaCoordinate * ConcreteFermion.beta * gammaCoordinateᴴ) * (R 1 2)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [hr, gamma_conjugates]
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [R, RZ, axisPerm, Equiv.swap_apply_def, OrthogonalRootPhase.realMatrix,
        ConcreteFermion.gamma, ConcreteFermion.alpha, mul_apply, conjTranspose_apply,
        Fin.sum_univ_four]

/-- Conjugation of the completed beta pulse restores the full invisible sector,
including any motion induced there by the conjugating root word. -/
theorem conjugated_pulse (c : Fin 3) (p t : ℝ)
    (Q : Matrix (Carrier c) (Carrier c) ℂ) (S B : Matrix (Fin 4) (Fin 4) ℂ)
    (ho : NativeObservation.Obs (embedding c) Q S)
    (hu : Q ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ))
    (hB : S * ConcreteFermion.beta * Sᴴ = B) (hp : 0 < p) (hp1 : p < 1/2) :
    Q * ClassBlindFlip.pulse c p t * Qᴴ = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation B (RootTransferPhase.gap p*t)) := by
  have hs : S*Sᴴ = 1 := (observed_unitary _ (isometry c) Q S ho hu).2
  rw [ClassBlindFlip.pulse_completed c p t hp hp1, conjugate_completion _ _ _ _ ho hu]
  congr 1
  simp only [LocalUnitary.rotation, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hs, hB]

def gammaPulse (c : Fin 3) (p t : ℝ) :=
  gammaConjugator c p * ClassBlindFlip.pulse c p t * (gammaConjugator c p)ᴴ

def alphaPulse (c : Fin 3) (p t : ℝ) (j : Fin 3) :=
  alphaConjugator c p j * ClassBlindFlip.pulse c p t * (alphaConjugator c p j)ᴴ

/-- Exact identity completion for the chiral internal rotation, in every class. -/
theorem gamma_completed (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    gammaPulse c p t = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation ConcreteFermion.gamma (RootTransferPhase.gap p*t)) :=
  conjugated_pulse c p t _ _ _ (gamma_observed c p hp hp1) (gamma_unitary c p hp hp1)
    gamma_conjugates hp hp1

/-- Exact identity completion for each spatial internal rotation, in every class. -/
theorem alpha_completed (c : Fin 3) (p t : ℝ) (j : Fin 3) (hp : 0 < p) (hp1 : p < 1/2) :
    alphaPulse c p t j = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation (ConcreteFermion.alpha j) (RootTransferPhase.gap p*t)) :=
  conjugated_pulse c p t _ _ _ (alpha_observed c p j hp hp1) (alpha_unitary c p j hp hp1)
    (alpha_conjugates j) hp hp1

theorem gammaPulse_unitary (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    gammaPulse c p t ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  rw [gamma_completed c p t hp hp1]
  exact IsometricDynamics.unitary _ (isometry c) _
    (LocalUnitary.rotation_unitary _ _ ConcreteFermion.gamma_hermitian ConcreteFermion.gamma_square)

theorem alphaPulse_unitary (c : Fin 3) (p t : ℝ) (j : Fin 3) (hp : 0 < p) (hp1 : p < 1/2) :
    alphaPulse c p t j ∈ unitary (Matrix (Carrier c) (Carrier c) ℂ) := by
  rw [alpha_completed c p t j hp hp1]
  exact IsometricDynamics.unitary _ (isometry c) _
    (LocalUnitary.rotation_unitary _ _ (ConcreteFermion.alpha_hermitian j) (ConcreteFermion.clifford.1 j))

lemma completed_fixes_even (c : Fin 3) (U : Matrix (Fin 4) (Fin 4) ℂ) :
    IsometricDynamics.extend (embedding c) U * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  simp only [IsometricDynamics.extend, Matrix.add_mul, Matrix.mul_assoc,
    IsometricDynamics.complement_right _ (isometry c), Matrix.mul_zero, zero_add,
    IsometricDynamics.complement_square _ (isometry c)]

theorem gamma_fixes_even (c : Fin 3) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    gammaPulse c p t * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  rw [gamma_completed c p t hp hp1]
  exact completed_fixes_even c _

theorem alpha_fixes_even (c : Fin 3) (p t : ℝ) (j : Fin 3) (hp : 0 < p) (hp1 : p < 1/2) :
    alphaPulse c p t j * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  rw [alpha_completed c p t j hp hp1]
  exact completed_fixes_even c _

/-- Inverse pair controls also use forward primitive-root phases. -/
theorem pair_inverse_program (c : Fin 3) (p : ℝ) (a : Fin 3) (j k : Fin 4)
    (hp : 0 < p) (hp1 : p < 1/2) :
    (pairPulse c p a j k)ᴴ =
      RootTransferPhase.phase (rootEvent c a k) p (RootTransferPhase.quarterTime p) *
        RootTransferPhase.phase (rootEvent c a j) p (RootTransferPhase.quarterTime p) := by
  have h (n : Fin 4) :
      RootTransferPhase.phase (rootEvent c a n) p (-(3*RootTransferPhase.quarterTime p)) =
      RootTransferPhase.phase (rootEvent c a n) p (RootTransferPhase.quarterTime p) := by
    rw [inverse_forward _ (root_twice c a n) _ _ hp hp1]
    congr 1
    ring
  simp only [pairPulse, conjTranspose_mul, phase_adjoint _ (root_twice c a _), h]

/-- The fixed chirality-conjugator echo lies in the existing forward ledger's interval. -/
lemma gamma_time_interval (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    0 ≤ 7*RootTransferPhase.quarterTime p/2 ∧
      7*RootTransferPhase.quarterTime p/2 ≤ 8*RootTransferPhase.quarterTime p := by
  have h := RootTransferPhase.quarterTime_positive p hp hp1
  constructor <;> linarith

/-- The complete internal instruction alphabet; these are the existing matrices,
not a choice of particle identities or a claim about the spatial walk. -/
inductive Generator where
  | beta
  | gamma
  | alpha (j : Fin 3)

def coordinate : Generator → Matrix (Fin 4) (Fin 4) ℂ
  | .beta => ConcreteFermion.beta
  | .gamma => ConcreteFermion.gamma
  | .alpha j => ConcreteFermion.alpha j

def instruction (c : Fin 3) (p t : ℝ) : Generator → Matrix (Carrier c) (Carrier c) ℂ
  | .beta => ClassBlindFlip.pulse c p t
  | .gamma => gammaPulse c p t
  | .alpha j => alphaPulse c p t j

lemma instruction_completed (c : Fin 3) (p t : ℝ) (g : Generator)
    (hp : 0 < p) (hp1 : p < 1/2) :
    instruction c p t g = IsometricDynamics.extend (embedding c)
      (LocalUnitary.rotation (coordinate g) (RootTransferPhase.gap p*t)) := by
  cases g with
  | beta => exact ClassBlindFlip.pulse_completed c p t hp hp1
  | gamma => exact gamma_completed c p t hp hp1
  | alpha j => exact alpha_completed c p t j hp hp1

/-- Multiplication order follows the explicitly supplied word. -/
def run (c : Fin 3) (p : ℝ) (word : List (Generator × ℝ)) :=
  (word.map (fun s => instruction c p s.2 s.1)).prod

def wordReadout (p : ℝ) (word : List (Generator × ℝ)) :=
  (word.map (fun s => LocalUnitary.rotation (coordinate s.1) (RootTransferPhase.gap p*s.2))).prod

/-- Any finite internal word composes without a residual invisible-sector action. -/
theorem run_completed (c : Fin 3) (p : ℝ) (word : List (Generator × ℝ))
    (hp : 0 < p) (hp1 : p < 1/2) :
    run c p word = IsometricDynamics.extend (embedding c) (wordReadout p word) := by
  induction word with
  | nil => simp [run, wordReadout, IsometricDynamics.extend_one]
  | cons s word ih =>
    change instruction c p s.2 s.1 * run c p word =
      IsometricDynamics.extend (embedding c)
        (LocalUnitary.rotation (coordinate s.1) (RootTransferPhase.gap p*s.2) * wordReadout p word)
    rw [instruction_completed c p s.2 s.1 hp hp1, ih, IsometricDynamics.extend_mul _ (isometry c)]

theorem run_fixes_even (c : Fin 3) (p : ℝ) (word : List (Generator × ℝ))
    (hp : 0 < p) (hp1 : p < 1/2) :
    run c p word * IsometricDynamics.complement (embedding c) =
      IsometricDynamics.complement (embedding c) := by
  rw [run_completed c p word hp hp1]
  exact completed_fixes_even c _

end PMAction.RootCliffordCompletion
