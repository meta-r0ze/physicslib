import PMElementaryParticles.ElectricHeavyRecord

/-!
# Four exact electric records with two fixed kicks

A balanced two-bit bank receives controlled electric phases at angles
`3π/2` and `3π` in charge-generator units. A fixed four-port transform
decodes their joint record. Neither kick has a position-dependent phase
reference. Bank preparation, joint kicks and the decoder's primitive
realization remain requirements.
-/

noncomputable section
namespace PMElementaryParticles.ElectricFourPortRecord

open Matrix Real PMAction PMConstants.PacketGaugeActions
open HeavyFlipControl ElectricHeavyRecord

/-- The four characters are ordered neutral, electron, up, down. -/
def address (r : Record) : Fin 4 :=
  if r.1 then if r.2 then 1 else 0 else if r.2 then 3 else 2

theorem address_injective : Function.Injective address := by decide +kernel

def phase (t : ℝ) (c : Channels) : ℂ :=
  Complex.exp ((↑(t * q c : ℝ) : ℂ) * Complex.I)

private def roots : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

theorem phase_codes (c : Channels) :
    phase (3 * π / 2) c = roots (address (labelRecord c)) := by
  unfold phase
  rw [charge_from_bits]
  rcases labelRecord c with ⟨sector, position⟩
  cases sector <;> cases position
  · change Complex.exp ((↑(3 * π / 2 * ((2 / 3 : ℝ) - 0)) : ℂ) * Complex.I) = -1
    rw [show 3 * π / 2 * ((2 / 3 : ℝ) - 0) = π by ring, Complex.exp_pi_mul_I]
  · change Complex.exp ((↑(3 * π / 2 * ((2 / 3 : ℝ) - 1)) : ℂ) * Complex.I) = -Complex.I
    rw [show 3 * π / 2 * ((2 / 3 : ℝ) - 1) = -π / 2 by ring]
    push_cast
    exact Complex.exp_neg_pi_div_two_mul_I
  · change Complex.exp ((↑(3 * π / 2 * ((0 : ℝ) - 0)) : ℂ) * Complex.I) = 1
    simp
  · change Complex.exp ((↑(3 * π / 2 * ((0 : ℝ) - 1)) : ℂ) * Complex.I) = Complex.I
    rw [show 3 * π / 2 * ((0 : ℝ) - 1) = π / 2 - 2 * π by ring]
    push_cast
    rw [sub_mul, Complex.exp_sub, Complex.exp_pi_div_two_mul_I, Complex.exp_two_pi_mul_I, div_one]

theorem phase_double (t : ℝ) (c : Channels) : phase (2 * t) c = phase t c ^ 2 := by
  unfold phase
  rw [show ((↑(2 * t * q c : ℝ) : ℂ) * Complex.I) =
      (↑(t * q c : ℝ) : ℂ) * Complex.I + (↑(t * q c : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, pow_two]

/-- The rows enumerate the four paths through the two control bits. -/
def bank (x y : ℂ) : Fin 4 → ℂ := ![1 / 2, x / 2, y / 2, x * y / 2]

def kick (high : Bool) (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  diagonal (if high then ![1, 1, z, z] else ![1, z, 1, z])

theorem kick_bank (x y : ℂ) :
    kick true y *ᵥ (kick false x *ᵥ bank 1 1) = bank x y := by
  rw [Matrix.mulVec_mulVec]
  ext i
  simp only [kick, Bool.false_eq_true, ite_true, ite_false, diagonal_mul_diagonal,
    mulVec_diagonal]
  fin_cases i <;> simp [bank] <;> ring

/-- The fixed logical mixer with the four electric characters as columns. -/
def encoder : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => bank (roots j) (roots j ^ 2) i

theorem encoder_left_inverse : encoderᴴ * encoder = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [encoder, bank, roots, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      Complex.I_sq, Complex.star_def, Complex.conj_I, map_div₀, map_pow, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.I_sq]

set_option maxHeartbeats 800000 in
/-- The same decoder reads every label with two fixed kick times. -/
theorem read_exact (c : Channels) :
    encoderᴴ *ᵥ (kick true (phase (3 * π) c) *ᵥ
      (kick false (phase (3 * π / 2) c) *ᵥ bank 1 1)) =
        Pi.single (address (labelRecord c)) 1 := by
  have hdouble : phase (3 * π) c = phase (3 * π / 2) c ^ 2 :=
    (congrArg (fun t => phase t c) (show 3 * π = 2 * (3 * π / 2) by ring)).trans
      (phase_double _ c)
  rw [kick_bank, hdouble, phase_codes]
  let j := address (labelRecord c)
  change encoderᴴ *ᵥ bank (roots j) (roots j ^ 2) = Pi.single j 1
  have h : encoder *ᵥ Pi.single j 1 = bank (roots j) (roots j ^ 2) := by
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    _ = (encoderᴴ * encoder) *ᵥ Pi.single j 1 := by rw [← Matrix.mulVec_mulVec, h]
    _ = _ := by rw [encoder_left_inverse, one_mulVec]

theorem phase_opposite (t : ℝ) (c : Channels) :
    phase t (ControlledGluedRegister.opposite c) = phase t c := by
  rw [phase, phase, (same_wall_pair c).1]

/-- Separate factor flags on the balanced bank cost half the corresponding
standalone diagonal flag. Their sum uses precisely these two fixed kicks. -/
def exposureToll (c : Channels) : ℝ :=
  (DiagonalReadout.flag (3 * π / 2 * q c) + DiagonalReadout.flag (3 * π * q c)) / 2

open ProtocolToll in
theorem exposure_tolls (a : Fin 3) :
    exposureToll electronStatic = 3 / 4 ∧
      exposureToll (downStatic a) = 3 / 4 ∧
      exposureToll (upStatic a) = 1 / 2 ∧ exposureToll neutrinoStatic = 0 := by
  obtain ⟨he, hd, hu, hn⟩ := static_record_codes a
  change labelRecord electronStatic = (true, true) at he
  change labelRecord neutrinoStatic = (true, false) at hn
  have eval (c : Channels) :
      DiagonalReadout.flag (3 * π / 2 * q c) =
        (1 - (roots (address (labelRecord c))).re) / 2 := by
    have h := congrArg Complex.re (phase_codes c)
    simp only [phase, Complex.exp_ofReal_mul_I_re] at h
    rw [DiagonalReadout.flag, h]
  simp only [exposureToll, eval, phase_position, he, hd, hu, hn]
  norm_num [address, roots]

/-! The decoder factorization keeps the joint operation inside the record bank. -/

private def mixHigh : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1]

private def mixLow : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

private def swapBits : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

set_option maxHeartbeats 2000000 in
/-- First mix the high arm, then phase the doubly occupied arm by `−i`.
Mix the low arm and swap the output bits. The factor `1/2` normalizes the
two binary mixers. -/
theorem decoder_word :
    encoderᴴ = (1 / 2 : ℂ) • (swapBits * mixLow *
      (diagonal ![1, 1, 1, -Complex.I] * mixHigh)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [encoder, bank, roots, swapBits, mixLow, mixHigh, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four, diagonal_mul, Matrix.diagonal_apply, Complex.star_def,
      Complex.I_sq, Complex.conj_I, map_div₀, map_pow, map_ofNat] <;>
    ring_nf

private theorem kick_low (x : ℂ) : kick false x *ᵥ bank 1 1 = bank x 1 := by
  ext i
  fin_cases i <;> rw [kick, mulVec_diagonal] <;> simp [bank, div_eq_mul_inv]

private theorem exposure_flags (x y : ℂ) (hx : Complex.normSq x = 1) :
    CommonResponse.stateFlag (kick false x) (bank 1 1) = Complex.normSq (1 - x) / 8 ∧
      CommonResponse.stateFlag (kick true y) (bank x 1) = Complex.normSq (1 - y) / 8 := by
  have h0 : bank 1 1 - kick false x *ᵥ bank 1 1 = ![0, (1 - x) / 2, 0, (1 - x) / 2] := by
    rw [kick_low]
    ext i
    fin_cases i <;> simp [bank] <;> ring
  have h1 : bank x 1 - kick true y *ᵥ bank x 1 = ![0, 0, (1 - y) / 2, x * (1 - y) / 2] := by
    ext i
    fin_cases i <;> rw [Pi.sub_apply, kick, mulVec_diagonal] <;> simp [bank] <;> ring
  rw [CommonResponse.stateFlag, CommonResponse.stateFlag, h0, h1]
  norm_num [LinkExpansion.nsq_eq, Fin.sum_univ_four, Complex.normSq_div, Complex.normSq_mul, hx]
  constructor <;> ring

/-- The exposure ledger is the sum of the two executed factor flags. -/
theorem exposure_eq_flags (c : Channels) :
    CommonResponse.stateFlag (kick false (phase (3 * π / 2) c)) (bank 1 1) +
      CommonResponse.stateFlag (kick true (phase (3 * π) c))
        (kick false (phase (3 * π / 2) c) *ᵥ bank 1 1) = exposureToll c := by
  have hx : Complex.normSq (phase (3 * π / 2) c) = 1 := by
    rw [phase, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [kick_low]
  obtain ⟨hl, hh⟩ := exposure_flags _ _ hx
  rw [hl, hh, exposureToll, phase, phase,
    DiagonalReadout.normSq_one_sub_exp, DiagonalReadout.normSq_one_sub_exp]
  ring

end PMElementaryParticles.ElectricFourPortRecord
