import PMElementaryParticles.ElectricFourPortRecord

/-!
# A native implementation boundary for the electric decoder

Permutation words and reconstructed root phases acting on the four
occupied record states fix the uniform amplitude. Both the decoder and its
controlled quarter phase change the uniform line. This concerns literal
occupied ports, where the reconstructed phases act by bank permutations.
-/

noncomputable section
namespace PMElementaryParticles.ElectricDecoderBoundary

open Matrix PMAction ElectricFourPortRecord

abbrev BankMatrix := Matrix (Fin 4) (Fin 4) ℂ

private def uniform : Fin 4 → ℂ := fun _ => 1

private theorem perm_fixes_uniform (e : Equiv.Perm (Fin 4)) :
    e.permMatrix ℂ *ᵥ uniform = uniform := by
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- Even arbitrary permutations in the occupied bank have this restriction
on their spectral phases. Common scalar phases retain its uniform line. -/
theorem spectral_fixes_uniform (e : Equiv.Perm (Fin 4)) (z : ℂ) :
    InvolutionComparison.phase (e.permMatrix ℂ) z *ᵥ uniform = uniform := by
  rw [InvolutionComparison.phase, InvolutionSpectral.plus, InvolutionSpectral.minus,
    add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, add_mulVec, sub_mulVec,
    one_mulVec, perm_fixes_uniform]
  module

/-- Allow every spectral phase of a bank permutation, with an arbitrary
common scalar on each pulse. This includes the reconstructed root phases. -/
def phaseWord (word : List (Equiv.Perm (Fin 4) × ℂ × ℂ)) : BankMatrix :=
  (word.map (fun (e, z, scalar) => scalar • InvolutionComparison.phase (e.permMatrix ℂ) z)).prod

theorem phase_word_uniform (word : List (Equiv.Perm (Fin 4) × ℂ × ℂ)) :
    ∃ z : ℂ, phaseWord word *ᵥ uniform = z • uniform := by
  induction word with
  | nil => exact ⟨1, by simp [phaseWord]⟩
  | cons hd tl ih =>
    obtain ⟨s, hs⟩ := ih
    rcases hd with ⟨e, z, r⟩
    refine ⟨r * s, ?_⟩
    change (((r • InvolutionComparison.phase (e.permMatrix ℂ) z)) *
      phaseWord tl) *ᵥ uniform = _
    rw [← mulVec_mulVec, hs, mulVec_smul, smul_mulVec, spectral_fixes_uniform, smul_smul, mul_comm]

theorem phase_word_not_decoder (word : List (Equiv.Perm (Fin 4) × ℂ × ℂ)) :
    phaseWord word ≠ encoderᴴ := by
  intro h
  obtain ⟨s, hs⟩ := phase_word_uniform word
  have hseed : encoder *ᵥ Pi.single (0 : Fin 4) 1 = bank 1 1 := by
    rw [mulVec_single_one]
    change bank 1 ((1 : ℂ) ^ 2) = bank 1 1
    rw [one_pow]
  have hu : bank 1 1 = (1 / 2 : ℂ) • uniform := by
    ext i; fin_cases i <;> norm_num [bank, uniform]
  have ho : encoderᴴ *ᵥ bank 1 1 = Pi.single (0 : Fin 4) 1 := by
    rw [← hseed, mulVec_mulVec, encoder_left_inverse, one_mulVec]
  rw [hu, mulVec_smul, ← h, hs, smul_smul] at ho
  have h1 := congrFun ho (1 : Fin 4)
  have h0 := congrFun ho (0 : Fin 4)
  simp [uniform] at h1 h0
  rw [h1] at h0
  norm_num at h0

theorem phase_word_not_quarter (word : List (Equiv.Perm (Fin 4) × ℂ × ℂ)) :
    phaseWord word ≠ diagonal ![1, 1, 1, -Complex.I] := by
  intro h
  obtain ⟨s, hs⟩ := phase_word_uniform word
  rw [h] at hs
  have h0 := congrFun hs (0 : Fin 4)
  have h3 := congrFun hs (3 : Fin 4)
  simp [mulVec_diagonal, uniform] at h0 h3
  have he := congrArg Complex.re (h3.trans h0.symm)
  norm_num at he

end PMElementaryParticles.ElectricDecoderBoundary
