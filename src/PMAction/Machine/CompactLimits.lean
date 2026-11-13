import PMAction.Machine.SummedReference
import PMAction.CompactTransport

/-!
# The reference-sampled limits for transports of a C² connection

`ReferenceSampling.ref_limit` and `SummedReference.sum_limit` take a `C^{1,1}` connection and
links cubically consistent with it. `CompactTransport.compact_transport_premises` derives both for
the unitary transports of a compactly supported C² connection. These versions take that instead:
the links are the connection's transports, and nothing else is assumed about them.
-/

noncomputable section
namespace PMAction.CompactLimits
open Matrix VaryingFields LinkConsistency ReferenceSampling SummedReference
open scoped Matrix.Norms.L2Operator

variable {N r : ℕ}

/-- **Reference-sampled limit for the transports of a C² connection.** -/
theorem ref_limit_c2 {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ} (hA : ContDiff ℝ 2 A)
    (hcs : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1) (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => refDensity T x E toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * r) / 2) *
        ∑ μ, ∑ ν, ∑ i, ∑ k,
          ‖(fieldStrength A (fderiv ℝ A) x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2)) := by
  obtain ⟨L, K, hL0, hK, hd, hL, hc⟩ :=
    CompactTransport.compact_transport_premises hA hcs hskew T hT0 hTd hTu
  exact ref_limit hd hL0 (hL x) hskew T hTu hK (hc x) E hE toll m W

/-- **Summed-reference limit for the transports of a C² connection.** -/
theorem sum_limit_c2 {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ} (hA : ContDiff ℝ 2 A)
    (hcs : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x : V)
    (E : Matrix (Fin N) (Fin r) ℂ) (hE : Eᴴ * E = 1) (hr : 0 < r) (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => sumDensity T x E toll m W h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / 4) *
        ∑ μ, ∑ ν, ∑ i, ∑ k,
          ‖(fieldStrength A (fderiv ℝ A) x μ ν * E : Matrix (Fin N) (Fin r) ℂ) i k‖ ^ 2)) := by
  obtain ⟨L, K, hL0, hK, hd, hL, hc⟩ :=
    CompactTransport.compact_transport_premises hA hcs hskew T hT0 hTd hTu
  exact sum_limit hd hL0 (hL x) hskew T hTu hK (hc x) E hE hr toll m W

end PMAction.CompactLimits
