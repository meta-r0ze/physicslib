import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A real update fixes θ, and also forbids the measured CP violation

Paper II reconstructs the dynamics from a bijective update. Where that update is a permutation of
configurations its matrix is real; this module asks what reality alone does to the two CP phases.

* `real_update_commutes_conj`: a real update matrix commutes with complex conjugation of
  amplitudes. Conjugation is the antiunitary time reversal, so the update is T-symmetric and,
  with CPT, CP-symmetric.
* `theta_real_iff`: the weight `e^{iθ}` of the winding-one topological sector is real exactly
  when `θ ∈ πℤ`; `real_weights_iff`: all winding weights `e^{inθ}` are real exactly then. A real
  update therefore leaves only `θ = 0` or `θ = π`.
* `jarlskog_real`: the Jarlskog invariant `Im(V₀₁V₁₂V̄₀₂V̄₁₁)` of any real mixing matrix is zero.
  `cp_needs_complex_mixing`: a nonzero invariant, as the paper proposes and as measured
  (`J ≈ 3×10⁻⁵`), requires a non-real mixing amplitude.

So reality of the update cannot be the whole strong-CP mechanism: the same reality that forces
`θ ∈ {0, π}` forces `J = 0`. What would persist with both observations is a split: complex
amplitudes confined to flavour mixing, with the topological-sector weights and the arg of the
quark-mass determinant kept real (a Nelson–Barr-type structure). Deriving that confinement from
the substrate is the open premise; it is not supplied here.
-/

namespace PMConstants.CPPhases
open Complex ComplexConjugate

theorem real_update_commutes_conj {n : ℕ} (U : Fin n → Fin n → ℂ) (hU : ∀ i j, (U i j).im = 0)
    (v : Fin n → ℂ) (i : Fin n) :
    conj (∑ j, U i j * v j) = ∑ j, U i j * conj (v j) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, Complex.conj_eq_iff_im.mpr (hU i j)]

theorem theta_real_iff (θ : ℝ) :
    (Complex.exp (θ * I)).im = 0 ↔ ∃ n : ℤ, θ = n * Real.pi := by
  rw [Complex.exp_ofReal_mul_I_im, Real.sin_eq_zero_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn.symm⟩

theorem real_weights_iff (θ : ℝ) :
    (∀ n : ℤ, (Complex.exp (((n : ℝ) * θ : ℝ) * I)).im = 0) ↔ ∃ k : ℤ, θ = k * Real.pi := by
  constructor
  · intro h
    have := h 1
    simp only [Int.cast_one, one_mul] at this
    exact (theta_real_iff θ).mp this
  · rintro ⟨k, rfl⟩ n
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_eq_zero_iff]
    exact ⟨n * k, by push_cast; ring⟩

/-- Jarlskog invariant of a 3×3 mixing matrix. -/
def jarlskog (V : Fin 3 → Fin 3 → ℂ) : ℝ :=
  (V 0 1 * V 1 2 * conj (V 0 2) * conj (V 1 1)).im

theorem jarlskog_real (V : Fin 3 → Fin 3 → ℂ) (hV : ∀ i j, (V i j).im = 0) : jarlskog V = 0 := by
  have h : ∀ i j, V i j = ((V i j).re : ℂ) := fun i j => Complex.ext (by simp) (by simp [hV i j])
  unfold jarlskog
  rw [h 0 1, h 1 2, h 0 2, h 1 1]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem cp_needs_complex_mixing (V : Fin 3 → Fin 3 → ℂ) (hJ : jarlskog V ≠ 0) :
    ∃ i j, (V i j).im ≠ 0 := by
  by_contra h
  push Not at h
  exact hJ (jarlskog_real V h)

end PMConstants.CPPhases
