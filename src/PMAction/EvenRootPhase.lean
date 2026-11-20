import PMKAutomaton.Machine.OddCarrierPhase
import PMAction.CompletionSelection

/-! An invisible-sector test of the existing four-root phase circuit.
Its common odd-sector phase is retained, but a nonzero even mode acquires
the square of that phase. At the supplied i-phase gate this mode changes sign.
Physical phase admission and gate costs remain inputs. -/
noncomputable section
namespace PMAction.EvenRootPhase
open Matrix CarrierEvents CarrierParity OrthogonalRootPhase

/-- A quadratic, antipode-even carrier mode with sign changes under exactly
two of the specified orthogonal root reflections. -/
def witness (c : Fin 3) (v : Carrier c) : ℤ :=
  if c = 0 then (vector v 0 - vector v 1) * (vector v 0 + vector v 1)
  else if c = 1 then (vector v 0 - vector v 1) * (vector v 2 - vector v 3)
  else (vector v 0 - vector v 1) * (vector v 2 + vector v 3)

def negative (c : Fin 3) (j : Fin 4) : Prop :=
  j = 0 ∨ j = if c = 0 then 1 else if c = 1 then 2 else 3
instance (c : Fin 3) (j : Fin 4) : Decidable (negative c j) := inferInstanceAs (Decidable (_ ∨ _))

theorem witness_sign : ∀ c j (v : Carrier c),
    witness c (event c j v) = (if negative c j then -1 else 1) * witness c v := by
  decide +kernel

theorem witness_even : ∀ c (v : Carrier c), witness c (antipode c v) = witness c v := by
  decide +kernel

theorem witness_nonzero : ∀ c, ∃ v : Carrier c, witness c v ≠ 0 := by decide +kernel

def mode (c : Fin 3) : Carrier c → ℂ := fun v => (witness c v : ℂ)

theorem mode_nonzero (c : Fin 3) : mode c ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := witness_nonzero c
  have he := congrFun h v
  change (witness c v : ℂ) = 0 at he
  have hz : witness c v = 0 := by exact_mod_cast he
  exact hv hz

lemma event_mode (c : Fin 3) (j : Fin 4) :
    (event c j).permMatrix ℂ *ᵥ mode c = (if negative c j then -1 else 1 : ℂ) • mode c := by
  ext v
  rw [permMatrix_mulVec]
  change (witness c (event c j v) : ℂ) = _ * (witness c v : ℂ)
  rw [witness_sign]
  split_ifs <;> norm_cast

lemma phase_mode (c : Fin 3) (j : Fin 4) (p t : ℝ) :
    RootTransferPhase.phase (event c j) p t *ᵥ mode c =
      (if negative c j then Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I) else 1) • mode c := by
  rw [RootTransferPhase.phase_formula _ (event_involutive c j)]
  simp only [InvolutionSpectral.plus, InvolutionSpectral.minus,
    add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, event_mode]
  split_ifs <;> module

/-- The actual circuit's invisible-sector eigenphase for arbitrary p and t. -/
theorem circuit_mode (c : Fin 3) (p t : ℝ) :
    phase c p t *ᵥ mode c =
      Complex.exp (-(RootTransferPhase.gap p*t : ℝ)*Complex.I)^2 • mode c := by
  simp only [phase, ← mulVec_mulVec, phase_mode, mulVec_smul, smul_smul]
  fin_cases c <;> simp [negative, pow_two, mul_assoc]

lemma phaseI_coefficient (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    Complex.exp (-(RootTransferPhase.gap p*(3*RootTransferPhase.quarterTime p) : ℝ)*Complex.I) = Complex.I := by
  have h := OddCarrierPhase.phaseI_sector c p hp hp1
  rw [OddCarrierPhase.phaseI, OrthogonalRootPhase.phase_sector] at h
  have hc := congrArg (fun M => ((embedding c)ᴴ * M) 0 0) h
  simpa [Matrix.mul_smul, isometry] using hc

theorem phaseI_mode (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    OddCarrierPhase.phaseI c p *ᵥ mode c = -mode c := by
  rw [OddCarrierPhase.phaseI, circuit_mode, phaseI_coefficient c p hp hp1, pow_two, Complex.I_mul_I]
  module

theorem mode_invisible (c : Fin 3) : (embedding c)ᴴ *ᵥ mode c = 0 := by
  have he : (antipode c).permMatrix ℂ *ᵥ mode c = mode c := by
    ext v
    rw [permMatrix_mulVec]
    change (witness c (antipode c v) : ℂ) = (witness c v : ℂ)
    exact_mod_cast witness_even c v
  have hp : (embedding c * (embedding c)ᴴ) *ᵥ mode c = 0 := by
    rw [projector]
    simp [smul_mulVec, sub_mulVec, he]
  have h := congrArg (fun x => (embedding c)ᴴ *ᵥ x) hp
  simpa [mulVec_mulVec, ← Matrix.mul_assoc, isometry] using h

lemma extension_fixes_mode (c : Fin 3) (U : Matrix (Fin 4) (Fin 4) ℂ) :
    IsometricDynamics.extend (embedding c) U *ᵥ mode c = mode c := by
  simp [IsometricDynamics.extend, IsometricDynamics.complement, add_mulVec,
    sub_mulVec, ← mulVec_mulVec, mode_invisible]

def coordinateFactors (q : Fin 4 → ℂ) := factor 0 (q 0) * factor 1 (q 1) * factor 2 (q 2) * factor 3 (q 3)

set_option maxHeartbeats 1000000 in
lemma coordinate_values (q : Fin 4 → ℂ) :
    coordinateFactors q 0 0 - coordinateFactors q 0 1 = q 0 ∧
    coordinateFactors q 0 0 + coordinateFactors q 0 1 = q 1 ∧
    coordinateFactors q 2 2 - coordinateFactors q 2 3 = q 2 ∧
    coordinateFactors q 2 2 + coordinateFactors q 2 3 = q 3 := by
  norm_num [coordinateFactors, factor, InvolutionSpectral.plus, InvolutionSpectral.minus,
    R, realMatrix, mul_apply, Fin.sum_univ_four]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

lemma equal_phases_forced (q : Fin 4 → ℂ) (h : coordinateFactors q = Complex.I • 1) :
    ∀ j, q j = Complex.I := by
  have ht := coordinate_values q
  rw [h] at ht
  norm_num [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at ht
  intro j
  fin_cases j
  · exact ht.1.symm
  · exact ht.2.1.symm
  · exact ht.2.2.1.symm
  · exact ht.2.2.2.symm
def independentPhase (c : Fin 3) (p t : Fin 4 → ℝ) :=
  RootTransferPhase.phase (event c 0) (p 0) (t 0) *
    RootTransferPhase.phase (event c 1) (p 1) (t 1) *
    RootTransferPhase.phase (event c 2) (p 2) (t 2) *
    RootTransferPhase.phase (event c 3) (p 3) (t 3)

lemma independent_readout (c : Fin 3) (p t : Fin 4 → ℝ) :
    independentPhase c p t * embedding c = embedding c *
      coordinateFactors (fun j => Complex.exp (-(RootTransferPhase.gap (p j)*t j : ℝ)*Complex.I)) := by
  have pull (A B : Matrix (Carrier c) (Carrier c) ℂ)
      (A' B' : Matrix (Fin 4) (Fin 4) ℂ)
      (ha : A * embedding c = embedding c * A')
      (hb : B * embedding c = embedding c * B') :
      (A*B) * embedding c = embedding c * (A'*B') := by
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  have h01 := pull _ _ _ _ (phase_intertwining c 0 (p 0) (t 0))
    (phase_intertwining c 1 (p 1) (t 1))
  have h012 := pull _ _ _ _ h01 (phase_intertwining c 2 (p 2) (t 2))
  exact pull _ _ _ _ h012 (phase_intertwining c 3 (p 3) (t 3))

/-- Independent clocks and rates for the same four primitive-root pulses
also fail to realize the identity completion of the visible i phase. -/
theorem no_independent_i_completion (c : Fin 3) (p t : Fin 4 → ℝ) :
    independentPhase c p t ≠ IsometricDynamics.extend (embedding c)
      (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
  intro h
  have ho := independent_readout c p t
  rw [h, IsometricDynamics.intertwining _ (isometry c)] at ho
  simp only [Matrix.mul_smul, Matrix.mul_one] at ho
  have hf := congrArg (fun M => (embedding c)ᴴ * M) ho
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, isometry, one_mul] at hf
  have hi := equal_phases_forced _ hf.symm
  have hm : independentPhase c p t *ᵥ mode c = -mode c := by
    simp only [independentPhase, ← mulVec_mulVec, phase_mode, mulVec_smul, smul_smul]
    simp_rw [hi]
    fin_cases c <;> simp [negative, Complex.I_mul_I]
  rw [h, extension_fixes_mode] at hm
  apply mode_nonzero c
  ext v
  have hv := congrFun hm v
  change mode c v = -(mode c v) at hv
  change mode c v = 0
  linear_combination hv / 2

/-- The common-clock construction is a special case of the independent-pulse obstruction. -/
theorem no_i_completion (c : Fin 3) (p t : ℝ) :
    phase c p t ≠ IsometricDynamics.extend (embedding c)
      (Complex.I • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
  simpa only [independentPhase, OrthogonalRootPhase.phase] using
    no_independent_i_completion c (fun _ => p) (fun _ => t)

end PMAction.EvenRootPhase
