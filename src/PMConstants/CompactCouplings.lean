import PMConstants.ChainCouplings
import PMAction.CompactTransport

/-!
# The coupling limits for transports of a C² connection

`GaugeGroupFactor.event_limit`, `ReferenceStiffness.lepton_weak_limit` and
`ChainCouplings.colour_limit` take a `C^{1,1}` connection and links cubically consistent with it.
`PMAction.CompactTransport.compact_transport_premises` derives both for the unitary transports of a
compactly supported C² connection, so these versions drop them: the links are the connection's
transports, and nothing else is assumed about them.

For the native packet the links are such transports, with controls that follow from the
substrate (`PMAction.NativeConsistency.d4_configuration_consistent`). What stays a premise is
that each gauge factor's links are the transports of its connection.
-/

noncomputable section
namespace PMConstants.CompactCouplings
open Matrix PMAction VaryingFields LinkConsistency ReferenceSampling SummedReference
open scoped Matrix.Norms.L2Operator

/-- **Event-priced limit for the transports of a C² `u(N)` connection.** -/
theorem event_limit_c2 {N : ℕ} {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ} (hA : ContDiff ℝ 2 A)
    (hcs : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ)) (x : V)
    (toll : ℝ) (m : ℕ) (W : ℝ) :
    Filter.Tendsto (fun h => GaugeGroupFactor.eventDensity T x toll m W h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * N) / 2) *
        ∑ μ, ∑ ν, ∑ i, ∑ j, ‖fieldStrength A (fderiv ℝ A) x μ ν i j‖ ^ 2)) := by
  obtain ⟨L, K, hL0, hK, hd, hL, hc⟩ :=
    CompactTransport.compact_transport_premises hA hcs hskew T hT0 hTd hTu
  exact GaugeGroupFactor.event_limit hd hL0 (hL x) hskew T hTu hK (hc x) toll m W

/-- **The weak limit on the lepton doublet for the transports of a C² connection.** -/
theorem lepton_weak_limit_c2 {A : V → V →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ} (hA : ContDiff ℝ 2 A)
    (hcs : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (x : V)
    (toll : ℝ) (m : ℕ) (W g : ℝ) (f : Fin 4 → Fin 4 → Fin 3 → ℝ)
    (hF : ∀ μ ν, fieldStrength A (fderiv ℝ A) x μ ν =
      ∑ a, ((g * f μ ν a : ℝ) : ℂ) • (Complex.I • ReferenceStiffness.weakT a)) :
    Filter.Tendsto (fun h => refDensity T x (1 : Matrix (Fin 2) (Fin 2) ℂ) toll m W h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / (2 * (2 : ℕ)) / 2) *
        ((1 / 2) * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2))) := by
  obtain ⟨L, K, hL0, hK, hd, hL, hc⟩ :=
    CompactTransport.compact_transport_premises hA hcs hskew T hT0 hTd hTu
  exact ReferenceStiffness.lepton_weak_limit hd hL0 (hL x) hskew T hTu hK (hc x) toll m W g f hF

/-- **The colour limit for the transports of a C² `su(3)` connection.** -/
theorem colour_limit_c2 {G : Type*} [Fintype G] [DecidableEq G]
    {A : V → V →L[ℝ] Matrix (Fin 3) (Fin 3) ℂ} (hA : ContDiff ℝ 2 A)
    (hcs : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin 3) (Fin 3) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)) (x : V)
    (toll : ℝ) (m : ℕ) (W g : ℝ)
    (Tg : G → Matrix (Fin 3) (Fin 3) ℂ) (hT : ∀ a, (Tg a)ᴴ = Tg a)
    (htr : ∀ a b, trace (Tg a * Tg b) = if a = b then ((1 / 2 : ℝ) : ℂ) else 0)
    (f : Fin 4 → Fin 4 → G → ℝ)
    (hF : ∀ μ ν, fieldStrength A (fderiv ℝ A) x μ ν =
      ∑ a, ((g * f μ ν a : ℝ) : ℂ) • (Complex.I • Tg a)) :
    Filter.Tendsto (fun h => sumDensity T x (1 : Matrix (Fin 3) (Fin 3) ℂ) toll m W h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((toll * m * W / 4) * ((1 / 2) * g ^ 2 * ∑ μ, ∑ ν, ∑ a, f μ ν a ^ 2))) := by
  obtain ⟨L, K, hL0, hK, hd, hL, hc⟩ :=
    CompactTransport.compact_transport_premises hA hcs hskew T hT0 hTd hTu
  exact ChainCouplings.colour_limit hd hL0 (hL x) hskew T hTu hK (hc x) toll m W g Tg hT htr f hF

end PMConstants.CompactCouplings
