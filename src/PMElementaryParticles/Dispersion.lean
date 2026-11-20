import PMElementaryParticles.CoherentRing

/-!
# Plane waves for the coherent ring

A plane wave on `Fin n × (Unit ⊕ Unit)` is `exp(i k j) u(d)` with
`k = 2π m / n`.  The full-firing tick shifts the phase by
`diag(exp(-i k), exp(i k))` (the direction convention of `ringShift`) and then
applies the certified encounter.  The momentum block is therefore
`M = encounter x * diag(exp(-i k), exp(i k))`.
-/

noncomputable section
namespace PMElementaryParticles.Dispersion

open Matrix PMAction
open PMElementaryParticles.CoherentRing
open PMElementaryParticles.PhaseToRecord

/-- Wavenumber of momentum mode `m`. -/
noncomputable def waveNumber (n : ℕ) (m : Fin n) : ℝ :=
  2 * Real.pi * (m.val : ℝ) / (n : ℝ)

/-- Plane wave on the ring. -/
def planeWave (n : ℕ) (m : Fin n) (u : Unit ⊕ Unit → ℂ) :
    Fin n × (Unit ⊕ Unit) → ℂ :=
  fun p => Complex.exp (((waveNumber n m * (p.1.val : ℝ) : ℝ) : ℂ) * Complex.I) * u p.2

/-- Shift phase in the direction order `(inl, inr)`. -/
def shiftDiag (k : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  diagonal fun d =>
    match d with
    | Sum.inl _ => Complex.exp ((-(k : ℂ)) * Complex.I)
    | Sum.inr _ => Complex.exp ((k : ℂ) * Complex.I)

/-- Momentum block of the full-firing tick. -/
def M (x k : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  encounter x * shiftDiag k

theorem planeWave_exp_period (n : ℕ) (m : Fin n) (hn : (n : ℝ) ≠ 0) :
    Complex.exp (((waveNumber n m * (n : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have hk : waveNumber n m * (n : ℝ) = 2 * Real.pi * (m.val : ℝ) := by
    unfold waveNumber
    field_simp [hn]
  rw [hk]
  have h : (((2 * Real.pi * (m.val : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_nat_mul_two_pi_mul_I m.val

end PMElementaryParticles.Dispersion
