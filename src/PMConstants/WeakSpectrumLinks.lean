import PMConstants.MatterRunning
import PMConstants.FermionMassLaw
import PMAction.WeakVertex
import PMAction.WallDispersion

/-!
# Paper II's W-exchange vertex and exact wall spectrum, applied to Paper III

* `fermi_operator`, `reference_contact`: Paper III's reference W mass `m_W² = g²v²/4`
  (`MatterRunning.mWsq_eq`) fed into Paper II's tree-level W exchange (`WeakVertex`). The full
  four-fermion amplitude, not only its coefficient, tends at zero momentum transfer to the V−A
  contact amplitude with `G_F = 1/(√2 v²)`.
* `light_branch`, `heavy_branch`: at unit link (`y = 1`), the exact eight-component wall spectrum
  (`WallDispersion.two_dirac_particles`) has masses `m₋ = lightMass δ` and `m₊ = lightMass δ + 1`.
  These are `FermionMassLaw`'s light fermion (`DetuningMass.mass_relation`) and its heavy partner,
  each now a complete Dirac particle with two spin states of each energy sign.
-/

noncomputable section
namespace PMConstants.WeakSpectrumLinks
open PMAction Filter Topology

/-- The reference W mass. -/
def mW (g v : ℝ) : ℝ := Real.sqrt (MatterRunning.mWsq g v)

lemma mW_sq (g v : ℝ) : mW g v ^ 2 = g ^ 2 * v ^ 2 / 4 := by
  rw [mW, Real.sq_sqrt (by rw [MatterRunning.mWsq_eq]; positivity), MatterRunning.mWsq_eq]

lemma mW_ne (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) : mW g v ≠ 0 := by
  intro h
  have := mW_sq g v
  rw [h] at this
  have : g ^ 2 * v ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hg (pow_eq_zero_iff two_ne_zero |>.mp h1)
  · exact hv (pow_eq_zero_iff two_ne_zero |>.mp h1)

theorem fermi_operator (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) :
    WeakVertex.fermiG g (mW g v) = 1 / (Real.sqrt 2 * v ^ 2) :=
  WeakVertex.exchange_fermi g v _ hg hv (mW_sq g v)

/-- **The four-fermion operator from the reference.** -/
theorem reference_contact (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) {ιk ιp ιe ιb : Type*}
    (uk : ιk → Fin 4 → ℂ) (up : ιp → Fin 4 → ℂ) (ue : ιe → Fin 4 → ℂ) (vb : ιb → Fin 4 → ℂ)
    (x : (ιk × ιp) × (ιe × ιb)) :
    Tendsto (fun q => WeakVertex.exchange g (mW g v) q uk up ue vb x) (𝓝 0)
      (𝓝 (AmplitudeTrace.amp (1 / (Real.sqrt 2 * v ^ 2)) uk up ue vb x)) := by
  rw [← fermi_operator g v hg hv]
  exact WeakVertex.exchange_contact g _ (mW_ne g v hg hv) uk up ue vb x

lemma rr_one (δ : ℝ) : WallDispersion.rr δ 1 = 2 * Real.sqrt (δ ^ 2 + 1 / 4) := by
  rw [WallDispersion.rr, show (1 : ℝ) ^ 4 + 4 * 1 ^ 2 * δ ^ 2 = 2 ^ 2 * (δ ^ 2 + 1 / 4) by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- The light branch at unit link is `FermionMassLaw`'s light fermion. -/
theorem light_branch (δ : ℝ) :
    WallDispersion.massSqM δ 1 = DetuningMass.lightMass δ ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ δ ^ 2 + 1 / 4 by positivity)
  simp only [WallDispersion.massSqM, WallDispersion.rhoM, rr_one, DetuningMass.lightMass]
  linear_combination -hs

/-- The heavy branch at unit link is its partner, of mass `m + 1`. -/
theorem heavy_branch (δ : ℝ) :
    WallDispersion.massSqP δ 1 = (DetuningMass.lightMass δ + 1) ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ δ ^ 2 + 1 / 4 by positivity)
  simp only [WallDispersion.massSqP, WallDispersion.rhoP, rr_one, DetuningMass.lightMass]
  linear_combination -hs

end PMConstants.WeakSpectrumLinks
