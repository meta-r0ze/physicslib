import PMElementaryParticles.ElectricFourPortRecord
import PMAction.CompletedCarrierPhase
import PMAction.Machine.ClockPeriod

/-!
# The electric decoder on the four-coordinate carrier sector

The existing odd coordinate embedding supplies a different bank encoding.
Two paired root quarter phases give the marked half-bank phase for each
binary mixer. Conjugating one root phase by the completed low mixer
implements the single marked port. The common odd i phase restores the
two binary mixers' accumulated phase. All operations here are on one
carrier; the joint electric write on a payload and this bank remains open.
-/

noncomputable section
namespace PMElementaryParticles.ElectricCoordinateDecoder

open Matrix PMAction CarrierEvents CarrierParity PairedRootFlip
open ElectricFourPortRecord

private def pulse (c : Fin 3) (p : ℝ) (a : Fin 3) (j : Fin 4) :=
  RootTransferPhase.phase (rootEvent c a j) p (RootTransferPhase.quarterTime p)

private theorem pulse_obs (c : Fin 3) (p : ℝ) (a : Fin 3) (j : Fin 4)
    (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeObservation.Obs (embedding c) (pulse c p a j) (factor a j (-Complex.I)) := by
  rw [pulse, ← quarter_coeff p hp hp']
  exact root_phase_observed c a j p _

private def mixer {R : Type*} [Monoid R] (F : Fin 3 → Fin 4 → R) (high : Bool) : R :=
  let a : Fin 3 := if high then 0 else 1
  let b : Fin 3 := if high then 1 else 0
  let d := F a 2 * F a 3
  d * (F b 0 * F b 2) * d

private def mixerCoordinate (high : Bool) :=
  mixer (fun a j => factor a j (-Complex.I)) high

private def alpha : ℂ := (1 - Complex.I) / 2

set_option maxHeartbeats 2500000 in
private theorem mixer_coordinate (high : Bool) :
    mixerCoordinate high = alpha • (if high then mixHigh else mixLow) := by
  have diagonalPair (h : Bool) :
      let a : Fin 3 := if h then 0 else 1
      factor a 2 (-Complex.I) * factor a 3 (-Complex.I) =
        diagonal (if h then ![1, 1, -Complex.I, -Complex.I]
          else ![1, -Complex.I, 1, -Complex.I]) := by
    cases h <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [factor, R, RZ, OrthogonalRootPhase.realMatrix, axisPerm, Equiv.swap_apply_def,
        InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.mul_apply,
        Fin.sum_univ_four, Matrix.one_apply, Matrix.diagonal_apply, Complex.I_sq] <;>
      ring_nf
  simp only [mixerCoordinate, mixer]
  rw [diagonalPair high]
  cases high <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [alpha, factor, R, RZ, OrthogonalRootPhase.realMatrix, axisPerm, Equiv.swap_apply_def,
      InvolutionSpectral.plus, InvolutionSpectral.minus, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.vecMul, dotProduct, mixHigh, mixLow, Complex.I_sq] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

private def carrierMixer (c : Fin 3) (p : ℝ) (high : Bool) :=
  mixer (pulse c p) high

private theorem mixer_obs (c : Fin 3) (p : ℝ) (high : Bool)
    (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeObservation.Obs (embedding c) (carrierMixer c p high) (mixerCoordinate high) := by
  cases high <;>
    exact NativeObservation.mul
      (NativeObservation.mul (NativeObservation.mul (pulse_obs _ _ _ _ hp hp')
        (pulse_obs _ _ _ _ hp hp')) (NativeObservation.mul (pulse_obs _ _ _ _ hp hp')
        (pulse_obs _ _ _ _ hp hp'))) (NativeObservation.mul (pulse_obs _ _ _ _ hp hp')
        (pulse_obs _ _ _ _ hp hp'))

private def lastPort := diagonal ![(1 : ℂ), 1, 1, -Complex.I]

set_option maxHeartbeats 1800000 in
private theorem mark_coordinate :
    mixerCoordinate false * factor 0 2 (-Complex.I) * (mixerCoordinate false)ᴴ = lastPort := by
  rw [mixer_coordinate]
  simp only [Bool.false_eq_true, ite_false]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, smul_mul_smul_comm]
  have ha : alpha * star alpha = 1 / 2 := by
    simp [alpha]
    ring_nf
    norm_num [Complex.I_sq]
  rw [ha]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lastPort, factor, R, RZ, OrthogonalRootPhase.realMatrix, axisPerm,
      Equiv.swap_apply_def, InvolutionSpectral.plus, InvolutionSpectral.minus,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.diagonal_apply, mixLow, Complex.I_sq] <;> ring

private def carrierMark (c : Fin 3) (p : ℝ) :=
  carrierMixer c p false * pulse c p 0 2 * (carrierMixer c p false)ᴴ

private theorem mark_obs (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeObservation.Obs (embedding c) (carrierMark c p) lastPort := by
  rw [← mark_coordinate]
  exact NativeObservation.mul
    (NativeObservation.mul (mixer_obs c p false hp hp') (pulse_obs c p 0 2 hp hp'))
    (NativeObservation.star (mixer_obs c p false hp hp'))

private theorem swap_coordinate : R 2 2 = swapBits := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R, RZ, OrthogonalRootPhase.realMatrix, axisPerm, Equiv.swap_apply_def, swapBits]

/-- The executable algebraic decoder. The adjoint of a root quarter is
three forward quarters. The meaning of the clock parameter stays the same
as for the other completed carrier pulses. -/
def decoderPulse (c : Fin 3) (p : ℝ) :=
  CompletedCarrierPhase.phaseI c p * (rootEvent c 2 2).permMatrix ℂ *
    carrierMixer c p false * (carrierMark c p * carrierMixer c p true)

private theorem decoder_coordinate :
    ((Complex.I : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * swapBits *
      mixerCoordinate false * (lastPort * mixerCoordinate true) = encoderᴴ := by
  rw [mixer_coordinate, mixer_coordinate, decoder_word]
  simp only [lastPort, Bool.false_eq_true, ite_false, ite_true, Matrix.mul_smul, Matrix.smul_mul,
    smul_mul_smul_comm, Matrix.one_mul]
  have ha : Complex.I * alpha * alpha = 1 / 2 := by
    unfold alpha
    ring_nf
    norm_num [Complex.I_sq, pow_succ]
  rw [ha]

/-- On the odd-coordinate bank the whole decoder is observed exactly,
including the common phase. The even complement remains separate. -/
theorem decoder_observed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeObservation.Obs (embedding c) (decoderPulse c p) encoderᴴ := by
  have hI : NativeObservation.Obs (embedding c) (CompletedCarrierPhase.phaseI c p)
      (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [CompletedCarrierPhase.phase_completed c p hp hp']
    refine ⟨IsometricDynamics.intertwining _ (isometry c) _, ?_⟩
    simp [IsometricDynamics.extend, Matrix.mul_add, ← Matrix.mul_assoc, isometry,
      IsometricDynamics.complement_right]
  rw [← decoder_coordinate, ← swap_coordinate]
  exact NativeObservation.mul
    (NativeObservation.mul (NativeObservation.mul hI (root_observed c 2 2))
      (mixer_obs c p false hp hp'))
    (NativeObservation.mul (mark_obs c p hp hp') (mixer_obs c p true hp hp'))

private theorem pulse_unitary (c a : Fin 3) (j : Fin 4) (p : ℝ) :
    pulse c p a j ∈ unitary _ :=
  RootTransferPhase.phase_unitary _ (root_twice c a j) _ _

private theorem mixer_unitary (c : Fin 3) (p : ℝ) (high : Bool) :
    carrierMixer c p high ∈ unitary _ := by
  cases high <;>
    exact mul_mem (mul_mem (mul_mem (pulse_unitary _ _ _ _) (pulse_unitary _ _ _ _))
      (mul_mem (pulse_unitary _ _ _ _) (pulse_unitary _ _ _ _)))
      (mul_mem (pulse_unitary _ _ _ _) (pulse_unitary _ _ _ _))

theorem decoder_unitary (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    decoderPulse c p ∈ unitary _ := by
  have hL := mixer_unitary c p false
  have hM : carrierMark c p ∈ unitary _ :=
    mul_mem (mul_mem hL (pulse_unitary c 0 2 p)) (Unitary.star_mem hL)
  exact mul_mem (mul_mem (mul_mem (CompletedCarrierPhase.phase_unitary c p hp hp')
    (CarrierResponse.perm_unitary _)) hL) (mul_mem hM (mixer_unitary c p true))

/-- With the kicked bank in the coordinate encoding, the root program
writes the exact occupied output port. -/
theorem decoder_reads (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (label : PMConstants.PacketGaugeActions.Channels) :
    decoderPulse c p *ᵥ (embedding c *ᵥ (kick true (phase (3 * Real.pi) label) *ᵥ
        (kick false (phase (3 * Real.pi / 2) label) *ᵥ bank 1 1))) =
      embedding c *ᵥ Pi.single (address (HeavyFlipControl.labelRecord label)) 1 := by
  rw [Matrix.mulVec_mulVec, (decoder_observed c p hp hp').1,
    ← Matrix.mulVec_mulVec, read_exact]

/-- The inverse decoder prepares the balanced bank from the neutral
coordinate seed already occupied in the carrier. -/
theorem prepare_balanced (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    (decoderPulse c p)ᴴ *ᵥ (embedding c *ᵥ Pi.single (0 : Fin 4) 1) =
      embedding c *ᵥ bank 1 1 := by
  have h := NativeObservation.star (decoder_observed c p hp hp')
  rw [Matrix.conjTranspose_conjTranspose] at h
  have h0 : encoder *ᵥ Pi.single (0 : Fin 4) 1 = bank 1 1 := by
    rw [Matrix.mulVec_single_one]
    change bank 1 ((1 : ℂ) ^ 2) = bank 1 1
    rw [one_pow]
  rw [Matrix.mulVec_mulVec, h.1, ← Matrix.mulVec_mulVec, h0]

/-- An observed factor has the same state flag on the encoded carrier
as on the four coordinates. This applies separately to each primitive
root phase along the word. -/
theorem encoded_flag (c : Fin 3) {A : Matrix (Carrier c) (Carrier c) ℂ}
    {B : Matrix (Fin 4) (Fin 4) ℂ}
    (h : NativeObservation.Obs (embedding c) A B) (v : Fin 4 → ℂ) :
    CommonResponse.stateFlag A (embedding c *ᵥ v) = CommonResponse.stateFlag B v := by
  have pop (x : Fin 4 → ℂ) :
      CommonResponse.nsq (embedding c *ᵥ x) = CommonResponse.nsq x := by
    unfold CommonResponse.nsq
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, isometry,
      Matrix.one_mulVec]
  unfold CommonResponse.stateFlag
  rw [Matrix.mulVec_mulVec, h.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, pop]

/-! ### Cancel the repeated mixer on the occupied bank -/

private theorem mixLow_sq : mixLow * mixLow = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mixLow, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.one_apply]

private theorem mixer_square : mixerCoordinate false * mixerCoordinate false =
    -Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [mixer_coordinate, Bool.false_eq_true, ite_false, smul_mul_smul_comm, mixLow_sq]
  have h : alpha * alpha * 2 = -Complex.I := by
    unfold alpha
    ring_nf
    norm_num [Complex.I_sq]
    ring
  rw [smul_smul, h]

private theorem short_coordinate :
    swapBits * (factor 0 2 (-Complex.I) * (mixerCoordinate false)ᴴ * mixerCoordinate true) =
      encoderᴴ := by
  rw [← decoder_coordinate, ← mark_coordinate]
  calc
    _ = ((Complex.I : ℂ) * -Complex.I) •
        (swapBits * (factor 0 2 (-Complex.I) * (mixerCoordinate false)ᴴ * mixerCoordinate true)) := by
      rw [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    _ = ((Complex.I : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * swapBits *
        (mixerCoordinate false * mixerCoordinate false) *
          (factor 0 2 (-Complex.I) * (mixerCoordinate false)ᴴ * mixerCoordinate true) := by
      rw [mixer_square]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      rw [mul_comm Complex.I (-Complex.I)]
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem swap_square : swapBits * swapBits = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapBits, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

/-- The shortened root decoder leaves the bank in bit-reversed output order.
The repeated low mixer and scalar correction of the longer word cancel
on the occupied odd sector. -/
def shortDecoder (c : Fin 3) (p : ℝ) :=
  pulse c p 0 2 * (carrierMixer c p false)ᴴ * carrierMixer c p true

theorem short_observed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeObservation.Obs (embedding c) (shortDecoder c p) (swapBits * encoderᴴ) := by
  rw [← short_coordinate, ← Matrix.mul_assoc, swap_square, Matrix.one_mul]
  exact NativeObservation.mul
    (NativeObservation.mul (pulse_obs c p 0 2 hp hp') (NativeObservation.star (mixer_obs c p false hp hp')))
    (mixer_obs c p true hp hp')

theorem short_unitary (c : Fin 3) (p : ℝ) :
    shortDecoder c p ∈ unitary _ :=
  mul_mem (mul_mem (pulse_unitary c 0 2 p) (Unitary.star_mem (mixer_unitary c p false)))
    (mixer_unitary c p true)

/-- Class-partition and root index, followed by the inverse-quarter bit.
A word is stored in matrix-product order (rightmost instruction fires first). -/
abbrev Instruction := Fin 3 × Fin 4 × Bool

def quarters (i : Instruction) : ℕ := if i.2.2 then 3 else 1

def runInstruction (c : Fin 3) (p : ℝ) (i : Instruction) :=
  RootTransferPhase.phase (rootEvent c i.1 i.2.1) p ((quarters i : ℝ) * RootTransferPhase.quarterTime p)

def readInstruction (i : Instruction) : Matrix (Fin 4) (Fin 4) ℂ :=
  factor i.1 i.2.1 (if i.2.2 then Complex.I else -Complex.I)

theorem instruction_observed (c : Fin 3) (p : ℝ) (i : Instruction)
    (hp : 0 < p) (hp' : p < 1 / 2) :
    NativeObservation.Obs (embedding c) (runInstruction c p i) (readInstruction i) := by
  rcases i with ⟨a, j, b⟩
  cases b
  · simpa [runInstruction, quarters, readInstruction, pulse] using pulse_obs c p a j hp hp'
  · have h := root_phase_observed c a j p (3 * RootTransferPhase.quarterTime p)
    rw [EvenRootPhase.phaseI_coefficient c p hp hp'] at h
    simpa [runInstruction, quarters, readInstruction] using h

private def mixerWord (high : Bool) : List Instruction :=
  let a : Fin 3 := if high then 0 else 1
  let b : Fin 3 := if high then 1 else 0
  [(a, 2, false), (a, 3, false), (b, 0, false), (b, 2, false), (a, 2, false), (a, 3, false)]

def shortWord : List Instruction :=
  (0, 2, false) :: (mixerWord false).reverse.map (fun i => (i.1, i.2.1, !i.2.2)) ++ mixerWord true

private theorem adjoint_quarter (c a : Fin 3) (p : ℝ) (j : Fin 4)
    (hp : 0 < p) (hp' : p < 1 / 2) :
    (pulse c p a j)ᴴ = runInstruction c p (a, j, true) := by
  rw [pulse, phase_adjoint _ (root_twice c a j), inverse_forward _ (root_twice c a j) _ _ hp hp']
  simp [runInstruction, quarters]
  congr 1
  ring

theorem short_word_exact (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    (shortWord.map (runInstruction c p)).prod = shortDecoder c p := by
  simp only [shortWord, mixerWord, shortDecoder, carrierMixer, mixer, Matrix.conjTranspose_mul,
    adjoint_quarter c _ p _ hp hp', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append,
    Bool.false_eq_true, Bool.not_false, ite_false, ite_true, Matrix.mul_one]
  simp only [Matrix.mul_assoc, runInstruction, quarters, pulse, Bool.false_eq_true,
    ite_false, ite_true, Nat.cast_one, one_mul]

/-- Occupied-bank decoding costs twenty-five root quarter-times before
including controlled electric kicks, reset, or a canonicalizing swap. -/
theorem short_duration : (shortWord.map quarters).sum = 25 := by decide +kernel

/-- Physical output spelling of the shortened decoder. -/
def shortPort (record : HeavyFlipControl.Record) : Fin 4 :=
  Equiv.swap 1 2 (address record)

/-- The port itself supplies the record under the reversed bit convention. -/
def recordAtPort (j : Fin 4) : HeavyFlipControl.Record :=
  (decide (j.val % 2 = 0), decide (2 ≤ j.val))

theorem record_at_short_port : ∀ r, recordAtPort (shortPort r) = r := by decide +kernel

private theorem swap_basis (j : Fin 4) :
    swapBits *ᵥ Pi.single j 1 = Pi.single (Equiv.swap 1 2 j) 1 := by
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.col_apply, swapBits, Pi.single_apply, Equiv.swap_apply_def]

/-- Applied after the two electric kicks, the short word writes the
same four exact records at bit-reversed ports. -/
theorem short_reads (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (label : PMConstants.PacketGaugeActions.Channels) :
    shortDecoder c p *ᵥ (embedding c *ᵥ (kick true (phase (3 * Real.pi) label) *ᵥ
        (kick false (phase (3 * Real.pi / 2) label) *ᵥ bank 1 1))) =
      embedding c *ᵥ Pi.single (shortPort (HeavyFlipControl.labelRecord label)) 1 := by
  rw [Matrix.mulVec_mulVec, (short_observed c p hp hp').1,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, read_exact, swap_basis, shortPort]

/-- The same preparation contract as the longer decoder, using the
neutral coordinate seed and the inverse of the shortened word. -/
theorem short_prepares (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    (shortDecoder c p)ᴴ *ᵥ (embedding c *ᵥ Pi.single (0 : Fin 4) 1) =
      embedding c *ᵥ bank 1 1 := by
  have h := NativeObservation.star (short_observed c p hp hp')
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  have hs : swapBitsᴴ *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1 := by
    rw [mulVec_single_one]
    ext i
    fin_cases i <;> norm_num [Matrix.col_apply, swapBits, Pi.single_apply]
  have h0 : encoder *ᵥ Pi.single (0 : Fin 4) 1 = bank 1 1 := by
    rw [Matrix.mulVec_single_one]
    change bank 1 ((1 : ℂ) ^ 2) = bank 1 1
    rw [one_pow]
  rw [Matrix.mulVec_mulVec, h.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, h0]

private def reversePhase (i : Instruction) : Instruction := (i.1, i.2.1, !i.2.2)

def undoWord : List Instruction := shortWord.reverse.map reversePhase

private theorem instruction_adjoint (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (i : Instruction) : (runInstruction c p i)ᴴ = runInstruction c p (reversePhase i) := by
  rcases i with ⟨a, j, b⟩
  cases b
  · simpa [runInstruction, quarters, reversePhase, pulse] using adjoint_quarter c a p j hp hp'
  · have h := congrArg Matrix.conjTranspose (adjoint_quarter c a p j hp hp')
    rw [Matrix.conjTranspose_conjTranspose] at h
    simpa [runInstruction, quarters, reversePhase, pulse] using h.symm

theorem undo_word_exact (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    (undoWord.map (runInstruction c p)).prod = (shortDecoder c p)ᴴ := by
  have h (w : List Instruction) : (w.reverse.map reversePhase |>.map (runInstruction c p)).prod =
      ((w.map (runInstruction c p)).prod)ᴴ := by
    induction w with
    | nil => simp
    | cons i w ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one,
        Matrix.conjTranspose_mul, ih, instruction_adjoint c p hp hp']
  rw [← short_word_exact c p hp hp']
  exact h shortWord

theorem undo_duration : (undoWord.map quarters).sum = 27 := by decide +kernel

/-- A one-frame serial schedule with fresh bank preparation cannot fit
when every root quarter-time is at least one substrate tick. -/
theorem fresh_bank_serial_exceeds_clock (p : ℝ) (h : 1 ≤ RootTransferPhase.quarterTime p) :
    (Delta : ℝ) < (((undoWord.map quarters).sum + (shortWord.map quarters).sum : ℕ) : ℝ) *
      RootTransferPhase.quarterTime p := by
  rw [undo_duration, short_duration]
  change (43 : ℝ) < 52 * RootTransferPhase.quarterTime p
  linarith

end PMElementaryParticles.ElectricCoordinateDecoder
