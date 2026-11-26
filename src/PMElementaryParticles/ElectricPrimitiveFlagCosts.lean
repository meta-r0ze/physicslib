import PMElementaryParticles.ElectricCoordinateDecoder
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Primitive phase flags of the shortened electric decoder

The ledger follows the executed root phases, from the already kicked odd bank.
A Gaussian-integer recurrence doubles every amplitude after a pulse so the
finite calculation is exact. Its price is the sum of the individual state
flags. The electric exposures use the previously checked two-kick ledger.
Seed supply, the physical joint kicks, and export/reset remain separate.
-/

noncomputable section
namespace PMElementaryParticles.ElectricPrimitiveFlagCosts

open Matrix PMAction ElectricCoordinateDecoder ElectricFourPortRecord
open PMConstants.PacketGaugeActions

private abbrev Vec := Fin 4 → ℂ
private abbrev GVec := Fin 4 → GaussianInt

/-- State flags in chronological order. -/
def flagLedger {n : Type*} [Fintype n] [DecidableEq n] :
    List (Matrix n n ℂ) → (n → ℂ) → ℝ
  | [], _ => 0
  | A :: tail, v => CommonResponse.stateFlag A v + flagLedger tail (A *ᵥ v)

private theorem nsq_scale (s : ℂ) (v : Vec) :
    CommonResponse.nsq (s • v) = Complex.normSq s * CommonResponse.nsq v := by
  simp only [LinkExpansion.nsq_eq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]

private theorem flag_scale (s : ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) (v : Vec) :
    CommonResponse.stateFlag A (s • v) = Complex.normSq s * CommonResponse.stateFlag A v := by
  rw [CommonResponse.stateFlag, CommonResponse.stateFlag, Matrix.mulVec_smul,
    ← smul_sub, nsq_scale]
  ring

private theorem ledger_scale (s : ℂ) (word : List (Matrix (Fin 4) (Fin 4) ℂ)) (v : Vec) :
    flagLedger word (s • v) = Complex.normSq s * flagLedger word v := by
  induction word generalizing v with
  | nil => simp [flagLedger]
  | cons A tail ih =>
    simp only [flagLedger, flag_scale, Matrix.mulVec_smul, ih, mul_add]

private def iG : GaussianInt := ⟨0, 1⟩

private theorem cast_iG : (iG : ℂ) = Complex.I := by
  simp [iG, GaussianInt.toComplex_def']

private def castVec (v : GVec) : Vec := fun i => GaussianInt.toComplex (v i)

private def reflected (s : Instruction) (v : GVec) : GVec :=
  fun j => ∑ k, ((PairedRootFlip.RZ s.1 s.2.1 j k : ℤ) : GaussianInt) * v k

private theorem cast_reflected (s : Instruction) (v : GVec) :
    castVec (reflected s v) = PairedRootFlip.R s.1 s.2.1 *ᵥ castVec v := by
  ext j
  simp [castVec, reflected, Matrix.mulVec, dotProduct, PairedRootFlip.R, map_sum]

private def doubledStep (s : Instruction) (v : GVec) : GVec :=
  let z := if s.2.2 then iG else -iG
  fun j => (1 + z) * v j + (1 - z) * reflected s v j

private theorem cast_doubled (s : Instruction) (v : GVec) :
    castVec (doubledStep s v) = (2 : ℂ) • (readInstruction s *ᵥ castVec v) := by
  have hz : ((if s.2.2 then iG else -iG : GaussianInt) : ℂ) =
      if s.2.2 then Complex.I else -Complex.I := by
    split <;> simp [cast_iG, GaussianInt.toComplex_neg]
  ext j
  change GaussianInt.toComplex ((1 + (if s.2.2 then iG else -iG)) * v j +
      (1 - (if s.2.2 then iG else -iG)) * reflected s v j) = _
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one, hz]
  change _ + _ * castVec (reflected s v) j = _
  rw [cast_reflected]
  simp only [readInstruction, PairedRootFlip.factor, InvolutionSpectral.plus,
    InvolutionSpectral.minus, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, castVec]
  ring

private def jumpSq (s : Instruction) (v : GVec) : ℤ :=
  ∑ j, ((v j - reflected s v j).re ^ 2 + (v j - reflected s v j).im ^ 2)

private theorem jump_sq_cast (s : Instruction) (v : GVec) :
    (jumpSq s v : ℝ) =
      CommonResponse.nsq (castVec v - PairedRootFlip.R s.1 s.2.1 *ᵥ castVec v) := by
  rw [← cast_reflected, LinkExpansion.nsq_eq]
  unfold jumpSq
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.sub_apply]
  change _ = Complex.normSq (GaussianInt.toComplex (v j) - GaussianInt.toComplex (reflected s v j))
  rw [← map_sub, Complex.normSq_apply]
  simp [pow_two]

private theorem factor_flag (s : Instruction) (v : Vec) :
    CommonResponse.stateFlag (readInstruction s) v =
      CommonResponse.nsq (v - PairedRootFlip.R s.1 s.2.1 *ᵥ v) / 8 := by
  let z : ℂ := if s.2.2 then Complex.I else -Complex.I
  have hz : Complex.normSq ((1 - z) / 2) = 1 / 2 := by
    unfold z
    split <;>
      norm_num [Complex.normSq_div, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  have h : v - readInstruction s *ᵥ v =
      ((1 - z) / 2) • (v - PairedRootFlip.R s.1 s.2.1 *ᵥ v) := by
    simp only [readInstruction, PairedRootFlip.factor, InvolutionSpectral.plus,
      InvolutionSpectral.minus, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, z]
    module
  rw [CommonResponse.stateFlag, h, nsq_scale, hz]
  ring

/-- In a doubled representation the tail's quadratic cost is four times
its physical cost. The recurrence uses rational arithmetic only. -/
private def exactLedger : List Instruction → GVec → ℚ
  | [], _ => 0
  | s :: tail, v => (jumpSq s v : ℚ) / 8 + exactLedger tail (doubledStep s v) / 4

private theorem exact_ledger_cast (word : List Instruction) (v : GVec) :
    (exactLedger word v : ℝ) = flagLedger (word.map readInstruction) (castVec v) := by
  induction word generalizing v with
  | nil => simp [exactLedger, flagLedger]
  | cons s tail ih =>
    simp only [exactLedger, Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat,
      List.map_cons, flagLedger, factor_flag, ih, cast_doubled, ledger_scale, jump_sq_cast]
    norm_num [Complex.normSq_ofNat]

private def rootCode (j : Fin 4) : GaussianInt := ![1, iG, -1, -iG] j

private def numerator (j : Fin 4) : GVec :=
  let z := rootCode j
  ![1, z, z ^ 2, z ^ 3]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem ledger_certificate : ∀ j : Fin 4,
    exactLedger shortWord.reverse (numerator j) = ![(4 : ℚ), 9, 6, 7] j := by
  decide +kernel

private theorem cast_root_code (c : Channels) :
    (rootCode (address (HeavyFlipControl.labelRecord c)) : ℂ) = phase (3 * Real.pi / 2) c := by
  rw [phase_codes]
  generalize address (HeavyFlipControl.labelRecord c) = j
  fin_cases j <;> simp [rootCode, cast_iG, GaussianInt.toComplex_neg] <;> rfl

private theorem encoded_input (c : Channels) :
    (1 / 2 : ℂ) • castVec (numerator (address (HeavyFlipControl.labelRecord c))) =
      bank (phase (3 * Real.pi / 2) c) (phase (3 * Real.pi / 2) c ^ 2) := by
  have hz := cast_root_code c
  ext i
  fin_cases i <;> simp [castVec, numerator, bank, map_pow, hz] <;> ring

/-- Exact sum of primitive phase flags on the two-kick input. -/
theorem primitive_decoder_flags (c : Channels) :
    flagLedger (shortWord.reverse.map readInstruction)
        (bank (phase (3 * Real.pi / 2) c) (phase (3 * Real.pi / 2) c ^ 2)) =
      ![(1 : ℝ), 9 / 4, 3 / 2, 7 / 4] (address (HeavyFlipControl.labelRecord c)) := by
  rw [← encoded_input, ledger_scale, ← exact_ledger_cast]
  have hc := ledger_certificate (address (HeavyFlipControl.labelRecord c))
  rw [hc]
  generalize address (HeavyFlipControl.labelRecord c) = j
  fin_cases j <;> norm_num [Complex.normSq_div]

/-- Isometric observation preserves the flag sum step by step, including
the state passed to the next primitive pulse. -/
theorem ledger_observed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (word : List Instruction) (v : Vec) :
    flagLedger (word.map (runInstruction c p)) (CarrierParity.embedding c *ᵥ v) =
      flagLedger (word.map readInstruction) v := by
  induction word generalizing v with
  | nil => rfl
  | cons s tail ih =>
    have h := instruction_observed c p s hp hp'
    simp only [List.map_cons, flagLedger]
    rw [encoded_flag c h, Matrix.mulVec_mulVec, h.1, ← Matrix.mulVec_mulVec, ih]

/-- The certified decoder costs hold on the actual occupied carrier
under the same root-time calibration as the short word. -/
theorem decoder_carrier_flags (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2)
    (label : Channels) :
    flagLedger (shortWord.reverse.map (runInstruction c p))
        (CarrierParity.embedding c *ᵥ
          bank (phase (3 * Real.pi / 2) label) (phase (3 * Real.pi / 2) label ^ 2)) =
      ![(1 : ℝ), 9 / 4, 3 / 2, 7 / 4] (address (HeavyFlipControl.labelRecord label)) := by
  rw [ledger_observed c p hp hp', primitive_decoder_flags]

private def zeroSeed (j : Fin 4) : GaussianInt := if j = 0 then 1 else 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem preparation_certificate : exactLedger undoWord.reverse zeroSeed = 1 := by
  decide +kernel

/-- Preparation from the occupied clean coordinate seed costs one flag
under the same primitive accounting. It is common to all payloads. -/
theorem preparation_flags (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    flagLedger (undoWord.reverse.map (runInstruction c p))
        (CarrierParity.embedding c *ᵥ Pi.single (0 : Fin 4) 1) = 1 := by
  have h : castVec zeroSeed = Pi.single (0 : Fin 4) 1 := by
    ext i
    by_cases hi : i = 0 <;> simp [castVec, zeroSeed, hi]
  rw [ledger_observed c p hp hp', ← h, ← exact_ledger_cast, preparation_certificate]
  norm_num

/-- Electric exposures and the thirteen decoder pulses, with a
bit-reversed receiver and one registration per state flag. -/
def primitiveForwardFlagCost (c : Channels) : ℝ :=
  exposureFlagSum c + flagLedger (shortWord.reverse.map readInstruction)
    (bank (phase (3 * Real.pi / 2) c) (phase (3 * Real.pi / 2) c ^ 2))

open ProtocolFlagCosts in
theorem forward_tolls (a : Fin 3) :
    primitiveForwardFlagCost electronStatic = 3 ∧ primitiveForwardFlagCost (downStatic a) = 5 / 2 ∧
      primitiveForwardFlagCost (upStatic a) = 2 ∧ primitiveForwardFlagCost neutrinoStatic = 1 := by
  obtain ⟨he, hd, hu, hn⟩ := HeavyFlipControl.static_record_codes a
  obtain ⟨te, td, tu, tn⟩ := exposure_tolls a
  change HeavyFlipControl.labelRecord electronStatic = (true, true) at he
  change HeavyFlipControl.labelRecord neutrinoStatic = (true, false) at hn
  change HeavyFlipControl.labelRecord (downStatic a) = (false, true) at hd
  change HeavyFlipControl.labelRecord (upStatic a) = (false, false) at hu
  simp only [primitiveForwardFlagCost, primitive_decoder_flags, te, td, tu, tn, he, hd, hu, hn]
  norm_num [address]

open ProtocolFlagCosts in
/-- The bit-reversed circuit has both required strict gaps under this tariff. -/
theorem charged_ladder (a : Fin 3) :
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (primitiveForwardFlagCost electronStatic) <
        PersistenceMechanics.EffectiveAction.attenuationWeight 1 (primitiveForwardFlagCost (downStatic a)) ∧
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (primitiveForwardFlagCost (downStatic a)) <
        PersistenceMechanics.EffectiveAction.attenuationWeight 1 (primitiveForwardFlagCost (upStatic a)) := by
  obtain ⟨he, hd, hu, -⟩ := forward_tolls a
  rw [TollAmplitude.wireAmplitude_lt_iff, TollAmplitude.wireAmplitude_lt_iff, he, hd, hu]
  norm_num

private def outputSwapFlag (j : Fin 4) : ℝ :=
  CommonResponse.stateFlag swapBits (swapBits *ᵥ Pi.single j 1)

private theorem output_swap_flags (j : Fin 4) :
    outputSwapFlag j = ![(0 : ℝ), 1 / 2, 1 / 2, 0] j := by
  have hs : swapBits * swapBits = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [swapBits, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
  rw [outputSwapFlag, CommonResponse.stateFlag, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  fin_cases j <;> norm_num [LinkExpansion.nsq_eq, Fin.sum_univ_four, Matrix.col_apply,
    swapBits, Pi.sub_apply, Pi.single_apply, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

open ProtocolFlagCosts in
/-- The canonicalizing half pulse adds half a registration to up and zero
to down. The two become equal. -/
theorem canonical_tie (a : Fin 3) :
    primitiveForwardFlagCost (downStatic a) + outputSwapFlag (address (HeavyFlipControl.labelRecord (downStatic a))) =
      primitiveForwardFlagCost (upStatic a) + outputSwapFlag (address (HeavyFlipControl.labelRecord (upStatic a))) := by
  obtain ⟨-, hd, hu, -⟩ := HeavyFlipControl.static_record_codes a
  obtain ⟨-, td, tu, -⟩ := forward_tolls a
  norm_num [td, tu, output_swap_flags, address, hd, hu]

end PMElementaryParticles.ElectricPrimitiveFlagCosts
