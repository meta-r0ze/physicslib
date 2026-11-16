import PMAction.Machine.ReferenceSampling

/-!
# A reference-conditioned leg response cannot tell the two light classes apart

Task: find a wall-side magnitude asymmetry between the two light classes `s`, `c` (PMElementaryParticles
REVIEW, "Up/down over one wire"). Candidate: price a spinor leg by its response to the stationary
reference, the reference-sampled flag `refFlag E P = Re tr(Eᴴ(1 − P)E)/(2r)`
(`Machine.ReferenceSampling.ref_flag`).

* `flag_conj`: if a unitary `F` fixes the reference states (`Fᴴ E = E`) then
  `refFlag E (F P Fᴴ) = refFlag E P` for every unitary `P`.

A colour-axis reflection fixes the reference's axis (`PMElementaryParticles.DoubletReflection
.flip_keeps_reference_axis`) and exchanges the two spinor classes (`flip_spinor`, `flip_cospinor`),
and the native words intertwine the classes with one coordinate matrix (`Machine.CarrierWeyl
.intertwining`). So for a reference fixed by that reflection, an `s` leg and a `c` leg related by it
have the same flag: this whole family of reference-readout mechanisms gives no magnitude asymmetry.
A surviving mechanism needs a reference, preparation, projector or timing that the reflection does
not fix. Recorded as a negative result (2026-11).
-/

namespace PMAction.ReferenceLegSymmetry
open Matrix PMAction.ReferenceSampling

variable {N r : ℕ}

/-- **Conjugating the leg by a reference-fixing unitary leaves its flag unchanged.** -/
theorem flag_conj (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1)
    (F : Matrix (Fin N) (Fin N) ℂ) (hF : F ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (hFE : Fᴴ * E = E)
    (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) :
    refFlag E (F * P * Fᴴ) = refFlag E P := by
  have hFs : Fᴴ ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hF
  have hU : F * P * Fᴴ ∈ unitary (Matrix (Fin N) (Fin N) ℂ) :=
    mul_mem (mul_mem hF hP) hFs
  have hFF : F * Fᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem hF
  have hEF : Eᴴ * F = Eᴴ := by
    have := congrArg conjTranspose hFE
    simpa [conjTranspose_mul] using this
  rw [ref_flag E hE _ hU, ref_flag E hE P hP]
  have h1 : Eᴴ * (1 - F * P * Fᴴ) * E = (Eᴴ * F) * (1 - P) * (Fᴴ * E) := by
    calc Eᴴ * (1 - F * P * Fᴴ) * E = Eᴴ * (F * Fᴴ - F * P * Fᴴ) * E := by rw [hFF]
      _ = (Eᴴ * F) * (1 - P) * (Fᴴ * E) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [h1, hEF, hFE]

end PMAction.ReferenceLegSymmetry
