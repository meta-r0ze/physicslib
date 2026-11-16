import PMAction.WireMass

/-!
# The wire's light mode vanishes on the cycle resonance

`PMAction.WireMass.det_mass`: `det M = κ_R0 κ_R1 κ_R2 · (δ³ + κ_O0 κ_O1 κ_O2)`. Three on-site steps
(`δ³`) and one full cycle through the three labels (`κ_O0 κ_O1 κ_O2`) are the two ways back to the
start in three steps; when they cancel, `M` is singular and the wire has an exactly massless mode.

* `det_factor`: with `δ_c³ = −κ_O0 κ_O1 κ_O2`, `det M = κ_R0κ_R1κ_R2 (δ − δ_c)(δ² + δ δ_c + δ_c²)`, so
  near the resonance the light mass is linear in the offset `δ − δ_c`.
* `resonance_singular`: at `δ = δ_c` some nonzero vector is annihilated by `M`.

**Numerically (wire inputs `K = 1`, `k = α/2`, `tools/protocol_readout_scan.py`).** Every protocol's
fit of its light ratio puts `δ_O` within a few percent of the real resonance `δ_c = −k^{2/3} ≈ −0.0237`:
the light ratios are distances from the resonance, not separate scales. On the resonance the middle
to heavy ratio is the same for every protocol, `m₂/m₃ ≈ k^{2/3} = 0.0232`. The data (`m_s/m_b ≈ 0.020`,
`m_c/m_t ≈ 0.0037`, `m_μ/m_τ = 0.0595`) depart from it by a per-protocol weight on the heavy label
(PMElementaryParticles REVIEW, "The protocol readout").
-/

namespace PMElementaryParticles.WireResonance
open Matrix PMAction.WireMass

theorem det_factor (δ δc : ℂ) (κR κO : Fin 3 → ℂ) (hc : δc ^ 3 = -(κO 0 * κO 1 * κO 2)) :
    (mass δ κR κO).det = κR 0 * κR 1 * κR 2 * ((δ - δc) * (δ ^ 2 + δ * δc + δc ^ 2)) := by
  rw [det_mass]
  have : κO 0 * κO 1 * κO 2 = -δc ^ 3 := by rw [hc]; ring
  rw [this]; ring

theorem resonance_singular (δc : ℂ) (κR κO : Fin 3 → ℂ) (hc : δc ^ 3 = -(κO 0 * κO 1 * κO 2)) :
    ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ mass δc κR κO *ᵥ v = 0 := by
  have hdet : (mass δc κR κO).det = 0 := by
    rw [det_factor δc δc κR κO hc]; ring
  exact Matrix.exists_mulVec_eq_zero_iff.mpr hdet

end PMElementaryParticles.WireResonance
