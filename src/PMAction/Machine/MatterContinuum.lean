import PMAction.Machine.CompactLimits
import PMAction.ScalarTransport

/-!
# The substrate's matter hops in the continuum: covariant derivatives

`PMConstants`' running needs the substrate's charged matter fluctuations to be the continuum charged
fields whose heat kernels give the spin terms (`RunningResponse`, `LandauDegeneracy`). Their kinetic
operators come from the lattice hops: a matter hop along a root compares the transported field
`U Φ(x + hv)` with `Φ(x)`.

* `scalar_limit_c2`: for the transports of a compactly supported C² connection and a compactly
  supported C² field, the event-priced scalar density converges to
  `Z_φ Σ_μ ‖(∂_μ + A_μ)Φ(x)‖²`: the continuum charged-scalar kinetic term, with no separate
  `C^{1,1}` or link-consistency premise (`CompactTransport`).
* `spinor_hop`: a spinor hop weighted by a constant matrix `Γ` (a Dirac matrix along the root)
  is `h Γ (∂_v + A_v)Φ(x) + O(h²)`: the lattice Dirac term is the covariant Dirac operator to first
  order, for the same links and fields.

With `NativeConsistency`, the substrate's own links are such transports. So the scalar and spinor
matter fluctuations on the substrate have the continuum covariant kinetic operators `−D²` and
`γ·D`, the operators `RunningResponse` and `LandauDegeneracy` take the spectra of.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.MatterContinuum
open Matrix VaryingFields ScalarTransport
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-- **The scalar continuum limit for transports of a C² connection and a C² field.** -/
theorem scalar_limit_c2 {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ} (hA : ContDiff ℝ 2 A)
    (hcs : HasCompactSupport A) (hskew : ∀ y v, star (A y v) = -A y v)
    (T : V → V → ℝ → Matrix (Fin N) (Fin N) ℂ) (hT0 : ∀ y v, T y v 0 = 1)
    (hTd : ∀ y v s, HasDerivAt (T y v) (T y v s * A (y + s • v) v) s)
    (hTu : ∀ y v s, T y v s ∈ unitary (Matrix (Fin N) (Fin N) ℂ))
    {Φ : V → Col N} (hΦ : ContDiff ℝ 2 Φ) (hΦc : HasCompactSupport Φ) (x : V)
    (toll : ℝ) (m : ℕ) :
    Filter.Tendsto (fun h => scalarDensity T Φ x toll m h) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (3 / 4 * (toll * m) *
        ∑ μ, ∑ i, ‖covD A Φ (fderiv ℝ Φ) x (basis μ) i 0‖ ^ 2)) := by
  obtain ⟨L, K, hL0, hK, hd, hL, hc⟩ :=
    CompactTransport.compact_transport_premises hA hcs hskew T hT0 hTd hTu
  obtain ⟨hdΦ, ⟨LΦ, hLΦ0, hLΦ⟩, -, -⟩ := CompactTransport.c2_compact_data hΦ hΦc
  exact scalar_limit hd hL0 (hL x) hdΦ hLΦ0 (fun y => hLΦ y x) T hK (hc x) toll m

/-- **The spinor hop is the covariant Dirac term to first order.** -/
theorem spinor_hop {A : V → V →L[ℝ] Matrix (Fin N) (Fin N) ℂ}
    {DA : V → V →L[ℝ] (V →L[ℝ] Matrix (Fin N) (Fin N) ℂ)} {x : V} {L : ℝ}
    (hA : ∀ y, HasFDerivAt A (DA y) y) (hL0 : 0 ≤ L)
    (hL : ∀ y, ‖DA y - DA x‖ ≤ L * ‖y - x‖)
    {Φ : V → Col N} {DΦ : V → V →L[ℝ] Col N} {LΦ : ℝ}
    (hΦ : ∀ y, HasFDerivAt Φ (DΦ y) y) (hLΦ0 : 0 ≤ LΦ)
    (hLΦ : ∀ y, ‖DΦ y - DΦ x‖ ≤ LΦ * ‖y - x‖)
    (v : V) (U : ℝ → Matrix (Fin N) (Fin N) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hU : ∀ h, 0 < h → h ≤ 1 → ‖U h - link A x v h‖ ≤ K * h ^ 3)
    (Γ : Matrix (Fin N) (Fin N) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖Γ * (U h * Φ (x + h • v) - Φ x) - h • (Γ * (DΦ x v + A x v * Φ x))‖ ≤ C * h ^ 2 := by
  obtain ⟨C, hC, hb⟩ := covariant_expand hA hL0 hL hΦ hLΦ0 hLΦ v U hK hU
  refine ⟨‖Γ‖ * C, by positivity, fun h h0 h1 => ?_⟩
  have e : Γ * (U h * Φ (x + h • v) - Φ x) - h • (Γ * (DΦ x v + A x v * Φ x)) =
      Γ * ((U h * Φ (x + h • v) - Φ x) - h • (DΦ x v + A x v * Φ x)) := by
    simp only [Matrix.mul_sub, Matrix.mul_smul]
  rw [e]
  calc ‖Γ * ((U h * Φ (x + h • v) - Φ x) - h • (DΦ x v + A x v * Φ x))‖
      ≤ ‖Γ‖ * ‖(U h * Φ (x + h • v) - Φ x) - h • (DΦ x v + A x v * Φ x)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Γ‖ * (C * h ^ 2) := by gcongr; exact hb h h0 h1
    _ = ‖Γ‖ * C * h ^ 2 := by ring

end PMAction.MatterContinuum
