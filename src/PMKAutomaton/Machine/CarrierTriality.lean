import PMKAutomaton.Machine.CarrierParity
import PMKAutomaton.Machine.GluedRegister

/-!
# Triality on native carrier amplitudes

Triality gives a reversible relabeling between adjacent glue classes.
On the antipodal-odd sector its matrix is the glued triality matrix.
The six-root crossing realizes this relabeling on diagonal glued roots.
-/

noncomputable section
namespace PMKAutomaton.CarrierTriality

open Matrix PMAction CarrierEvents
open PMElementaryParticles

private def transportedBox {c : Fin 3} (v : Carrier c) : Box :=
  fun i => ⟨((GluedRegister.triality (vector v) i + 2).toNat) % 5, Nat.mod_lt _ (by decide)⟩

private theorem transported_valid : ∀ (c : Fin 3) (v : Carrier c),
    valid (c + 1) (transportedBox v) := by
  decide +kernel

private def nextCarrier (c : Fin 3) (v : Carrier c) : Carrier (c + 1) :=
  ⟨transportedBox v, transported_valid c v⟩

private theorem next_vector : ∀ (c : Fin 3) (v : Carrier c) (i : Fin 4),
    vector (nextCarrier c v) i = GluedRegister.triality (vector v) i := by
  decide +kernel

private theorem next_bijective : ∀ (c : Fin 3), Function.Bijective (nextCarrier c) := by
  decide +kernel

def carrierTriality (c : Fin 3) : Carrier c ≃ Carrier (c + 1) :=
  Equiv.ofBijective (nextCarrier c) (next_bijective c)

theorem carrierTriality_vector (c : Fin 3) (v : Carrier c) :
    vector (carrierTriality c v) = GluedRegister.triality (vector v) := by
  funext i
  exact next_vector c v i

/-- Triality in the antipodal-odd coordinate frame. -/
def trialityMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => (GluedRegister.M i j : ℂ) / 2

theorem triality_unitary : trialityMatrix ∈ unitary _ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [trialityMatrix, GluedRegister.M, star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem triality_cube : trialityMatrix * (trialityMatrix * trialityMatrix) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [trialityMatrix, GluedRegister.M, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

private theorem doubled_vector : ∀ (c : Fin 3) (v : Carrier c) (i : Fin 4),
    2 * vector (nextCarrier c v) i = ∑ j, GluedRegister.M i j * vector v j := by
  decide +kernel

private theorem moved_embedding (c : Fin 3) :
    (CarrierParity.embedding (c + 1)).submatrix (carrierTriality c) id =
      CarrierParity.embedding c * trialityMatrixᴴ := by
  ext v i
  change CarrierParity.scale * (vector (nextCarrier c v) i : ℂ) = _
  have h := congrArg (fun z : ℤ => (z : ℂ)) (doubled_vector c v i)
  push_cast at h
  rw [Matrix.mul_apply]
  change _ = ∑ j : Fin 4, (CarrierParity.scale * (vector v j : ℂ)) *
    star ((GluedRegister.M i j : ℂ) / 2)
  have hs (z : ℤ) : star ((z : ℂ) / 2) = (z : ℂ) / 2 := by
    rw [Complex.star_def]
    simp [map_ofNat]
  simp_rw [hs]
  simp_rw [show ∀ j : Fin 4,
      CarrierParity.scale * (vector v j : ℂ) * ((GluedRegister.M i j : ℂ) / 2) =
      (CarrierParity.scale / 2) * ((GluedRegister.M i j : ℂ) * (vector v j : ℂ)) by
    intro j
    ring]
  rw [← Finset.mul_sum, ← h]
  ring

/-- Relabeling actual carrier amplitudes by triality moves their odd coordinates
by the same matrix. This preserves all four coordinate amplitudes. -/
theorem triality_observed (c : Fin 3) (ψ : Fin 4 → ℂ) :
    (CarrierParity.embedding (c + 1) *ᵥ (trialityMatrix *ᵥ ψ)) ∘ carrierTriality c =
      CarrierParity.embedding c *ᵥ ψ := by
  have h : trialityMatrixᴴ * trialityMatrix = 1 := triality_unitary.1
  change (CarrierParity.embedding (c + 1)).submatrix (carrierTriality c) id *ᵥ
    (trialityMatrix *ᵥ ψ) = _
  rw [moved_embedding, Matrix.mulVec_mulVec, Matrix.mul_assoc, h, Matrix.mul_one]

/-- A single logical carrier occupying the diagonal of the glued root bank.
Its two equal coordinates specify one root label. -/
def diagonalRoot {c : Fin 3} (v : Carrier c) : GluedRegister.Wt × GluedRegister.Wt :=
  (vector v, vector v)

theorem carrier_is_glued : ∀ (x : Fin 3) (v : Carrier x),
    ∃ a : Fin 8, vector v = GluedRegister.carrier x a := by
  decide +kernel

/-- On the diagonal, the actual six-root crossing sends both halves to
the same new carrier. This implements the triality permutation on the
diagonal sector, including its linear action on an occupied odd seed. -/
theorem glued_triality_step (c : Fin 3) (v : Carrier c) :
    GluedRegister.runCrossing (diagonalRoot v) = diagonalRoot (carrierTriality c v) := by
  obtain ⟨a, ha⟩ := carrier_is_glued c v
  change GluedRegister.runCrossing (vector v, vector v) =
    (vector (nextCarrier c v), vector (nextCarrier c v))
  have hv : vector (nextCarrier c v) = GluedRegister.triality (vector v) := by
    funext i
    exact next_vector c v i
  rw [hv, ha, GluedRegister.crossing_word_glued]
  rfl

end PMKAutomaton.CarrierTriality
