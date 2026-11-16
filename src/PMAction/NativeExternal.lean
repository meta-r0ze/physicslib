import PMAction.WeakVertex
import PMAction.WallChiralCurrent
import PMAction.SpinorCompleteness

/-!
# Native external modes and their charged current are `AmplitudeTrace`'s spinors and bilinears

`AmplitudeTrace` and `WeakVertex` work with Dirac spinors in `ker(p̸ − m)` and bilinears
`ū γ^μ L w` built from `VATrace.g`. This module identifies both with native objects of the wall.

* `g_eq`: `VATrace.g` is exactly the gamma set `WallChiralCurrent.diracGamma` reconstructed from the
  wall Hamiltonian's own matrices (`γ⁰ = β`, `γʲ = β αⱼ`); `γ⁵ = Γ` is `WallChiralCurrent.gammaFive_eq`.
* `wall_block`: one wall's block of the native Hamiltonian at lattice momentum `k` with detuning `δ`,
  `Σⱼ sin kⱼ αⱼ + δ β`, is the Dirac Hamiltonian `Hd p δ = Σⱼ pⱼ αⱼ + δ β` at `p⃗ = sin k`.
* `kernel_iff_eigen`: `u ∈ ker(p̸ − m)` exactly when `Hd p m u = p₀ u`. So the external spinors of
  `AmplitudeTrace` are the eigenmodes of the native wall block with energy `p₀`, momentum `sin k` and
  mass the wall's detuning; the antiparticle kernel `ker(p̸ + m)` is the `−p₀` eigenmode at `−p⃗`.
* `native_current`: the native current operators are the density `1` and the velocities
  `αⱼ = ∂/∂pⱼ Hd` (`J`, `J_eq`: `J μ = γ⁰γ^μ`). Between any two modes,
  `u† J^μ P_L w = ū γ^μ P_L w`, the vertex bilinear of `WeakVertex.vertex` (with the charged
  projector `P_L = (1 − Γ)/2`, the wall projector's block, `WallChiralCurrent.projector_eq_fromBlocks_PL`).

Normalization: `AmplitudeTrace` takes each spinor family as `√(2p₀)` times an orthonormal basis of
its kernel; with unit-normalized native modes that factor is the Lorentz-invariant state count that
pairs with the measure `d³p/((2π)³ 2p₀)` (`ElectronMeasure`, `NullBoost`), so the rate is unchanged.
Not constructed here: which protocol channels are the final states (PMElementaryParticles).
-/

noncomputable section
namespace PMAction.NativeExternal
open Matrix ConcreteFermion VATrace SpinorCompleteness

theorem g_eq : ∀ μ, VATrace.g μ = WallChiralCurrent.diracGamma μ := by
  intro μ
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [VATrace.g, WallChiralCurrent.diracGamma, beta, alpha]

/-- The native current operators: density and the three velocities. -/
def J : Fin 4 → Spin := ![1, alpha 0, alpha 1, alpha 2]

theorem J_eq : ∀ μ, J μ = g 0 * g μ := by
  intro μ
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [J, VATrace.g, alpha, mul_apply, Fin.sum_univ_four]

/-- The Dirac Hamiltonian at spatial momentum `(p₁, p₂, p₃)` and mass `m`. -/
def Hd (p : Fin 4 → ℝ) (m : ℝ) : Spin :=
  (p 1 : ℂ) • alpha 0 + (p 2 : ℂ) • alpha 1 + (p 3 : ℂ) • alpha 2 + (m : ℂ) • beta

theorem wall_block (k : Fin 3 → ℝ) (δ E : ℝ) :
    DomainWallSpectrum.momentum alpha k + δ • beta =
      Hd ![E, Real.sin (k 0), Real.sin (k 1), Real.sin (k 2)] δ := by
  simp only [DomainWallSpectrum.momentum, Fin.sum_univ_three, Hd, Complex.coe_smul]
  rfl

lemma g0_D (p : Fin 4 → ℝ) (m : ℝ) :
    g 0 * D p m = (p 0 : ℂ) • (1 : Spin) - Hd p m := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [D, P, sl, cp, Hd, VATrace.g, alpha, beta, mul_apply, Fin.sum_univ_four,
      Matrix.sub_apply, Matrix.smul_apply, one_apply] <;> ring

lemma g0_sq : g 0 * g 0 = (1 : Spin) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [VATrace.g, mul_apply, Fin.sum_univ_four, one_apply]

/-- **External spinors are native eigenmodes.** -/
theorem kernel_iff_eigen (p : Fin 4 → ℝ) (m : ℝ) (u : Fin 4 → ℂ) :
    D p m *ᵥ u = 0 ↔ Hd p m *ᵥ u = (p 0 : ℂ) • u := by
  constructor
  · intro h
    have h' : (g 0 * D p m) *ᵥ u = 0 := by rw [← mulVec_mulVec, h, mulVec_zero]
    rw [g0_D, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h'
    exact h'.symm
  · intro h
    have h' : (g 0 * D p m) *ᵥ u = 0 := by
      rw [g0_D, sub_mulVec, smul_mulVec, one_mulVec, h, sub_self]
    have : (g 0 * (g 0 * D p m)) *ᵥ u = 0 := by rw [← mulVec_mulVec, h', mulVec_zero]
    rwa [← Matrix.mul_assoc, g0_sq, Matrix.one_mul] at this

/-- **The native charged current is the vertex bilinear.** -/
theorem native_current (μ : Fin 4) (u w : Fin 4 → ℂ) :
    star u ⬝ᵥ ((J μ * WeakVertex.PL) *ᵥ w) =
      AmplitudeTrace.bar u ⬝ᵥ ((g μ * WeakVertex.PL) *ᵥ w) := by
  rw [J_eq, AmplitudeTrace.bar, Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec]

end PMAction.NativeExternal
