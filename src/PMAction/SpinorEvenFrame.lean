import PMAction.Machine.VectorEvenFrame

/-!
# Complete even frame of the second glue class

The four antipodal pair sums of the actual spinor carriers form a complete
even frame, complementary to the existing coordinate-odd frame. Representatives
have first coordinate positive; their ordering is only a readout basis choice.
This is a proof basis inside the existing eight labels, not a new register or
physical allocation. It is used to check the class-blind root echo.
-/
noncomputable section
namespace PMAction.SpinorEvenFrame
open Matrix CarrierEvents
abbrev C := Carrier 1

def boxes : Fin 4 → Box := ![
  ![3,3,3,3], ![3,3,1,1], ![3,1,3,1], ![3,1,1,3]]
lemma boxes_valid : ∀ i, valid 1 (boxes i) := by decide +kernel

def representative (i : Fin 4) : C := ⟨boxes i, boxes_valid i⟩
def indicator (v : C) (i : Fin 4) : ℤ :=
  if v = representative i ∨ v = CarrierParity.antipode 1 (representative i) then 1 else 0

lemma pair_gram : ∀ i j : Fin 4,
    (∑ v : C, indicator v i * indicator v j) = if i = j then 2 else 0 := by decide +kernel
lemma carrier_gram : ∀ v w : C,
    (∑ i, indicator v i * indicator w i) =
      (if v = w then 1 else 0) + (if CarrierParity.antipode 1 v = w then 1 else 0) := by
  decide +kernel
lemma contrast_gram : ∀ i j : Fin 4,
    (∑ v : C, vector v i * indicator v j) = 0 := by decide +kernel

def embedding : Matrix C (Fin 4) ℂ := fun v i => VectorEvenFrame.scale * (indicator v i : ℂ)

theorem isometry : embeddingᴴ * embedding = 1 := by
  ext i j
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (pair_gram i j)
  push_cast at hg
  have he (v : C) : star (embedding v i) * embedding v j =
      (1/2 : ℂ) * ((indicator v i : ℂ) * (indicator v j : ℂ)) := by
    simp only [embedding, star_mul, star_intCast]
    calc
      _ = (star VectorEvenFrame.scale * VectorEvenFrame.scale) *
          ((indicator v i : ℂ) * (indicator v j : ℂ)) := by ring
      _ = _ := by rw [VectorEvenFrame.scale_sq]
  simp only [mul_apply, conjTranspose_apply]
  simp_rw [he]
  rw [← Finset.mul_sum, hg]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem projector : embedding * embeddingᴴ =
    (1/2 : ℂ) • (1 + (CarrierParity.antipode 1).permMatrix ℂ) := by
  ext v w
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (carrier_gram v w)
  push_cast at hg
  have he (i : Fin 4) : embedding v i * star (embedding w i) =
      (1/2 : ℂ) * ((indicator v i : ℂ) * (indicator w i : ℂ)) := by
    simp only [embedding, star_mul, star_intCast]
    calc
      _ = (star VectorEvenFrame.scale * VectorEvenFrame.scale) *
          ((indicator v i : ℂ) * (indicator w i : ℂ)) := by ring
      _ = _ := by rw [VectorEvenFrame.scale_sq]
  simp only [mul_apply, conjTranspose_apply]
  simp_rw [he]
  rw [← Finset.mul_sum, hg]
  by_cases hv : v = w
  · subst w
    norm_num [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, CarrierParity.no_fixed_antipode]
  · by_cases ha : CarrierParity.antipode 1 v = w <;>
      norm_num [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hv, ha]

theorem complete : CarrierParity.embedding 1 * (CarrierParity.embedding 1)ᴴ +
    embedding * embeddingᴴ = 1 := by
  rw [CarrierParity.projector, projector]
  module

theorem odd_orthogonal : (CarrierParity.embedding 1)ᴴ * embedding = 0 := by
  ext i j
  have hg := congrArg (fun z : ℤ => (z : ℂ)) (contrast_gram i j)
  push_cast at hg
  simp only [mul_apply, conjTranspose_apply, CarrierParity.embedding, embedding, star_mul,
    star_intCast, Matrix.zero_apply]
  have he (v : C) : (vector v i : ℂ) * star CarrierParity.scale *
      (VectorEvenFrame.scale * (indicator v j : ℂ)) =
      (star CarrierParity.scale * VectorEvenFrame.scale) *
        ((vector v i : ℂ) * (indicator v j : ℂ)) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, hg, mul_zero]

/-- Agreement on the complete odd and even frames determines the full operator. -/
theorem eq_of_frames (A B : Matrix C C ℂ)
    (ho : A * CarrierParity.embedding 1 = B * CarrierParity.embedding 1)
    (he : A * embedding = B * embedding) : A = B := by
  calc
    A = A * (CarrierParity.embedding 1 * (CarrierParity.embedding 1)ᴴ +
        embedding * embeddingᴴ) := by rw [complete, Matrix.mul_one]
    _ = B * (CarrierParity.embedding 1 * (CarrierParity.embedding 1)ᴴ +
        embedding * embeddingᴴ) := by
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, ho, he]
    _ = B := by rw [complete, Matrix.mul_one]

end PMAction.SpinorEvenFrame
