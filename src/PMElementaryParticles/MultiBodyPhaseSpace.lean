import PMElementaryParticles.CompositePhaseSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! **Massless three-body phase space.**

For three massless daughters,

```
Φ₃ = M² / (128π³).
```

This is the massless coefficient; massive multi-body phase space remains a
kinematic integral and is not constructed here.

The recursive **factorization** (review item A3) is `masslessThreeBody_factorization`:
`Φ₃(M) = (1/(2π)) ∫₀^{M²} Φ₂² ds` with `Φ₂ = 1/(8π)` the two-body factor
(`PolarMeasure.two_body_phase_space`) — the spectator invariant mass `s` runs to `M²`,
and `(1/(2π))·M²·(1/(8π))² = M²/(128π³)`.
-/

noncomputable section
namespace PMElementaryParticles.MultiBodyPhaseSpace

/-- Massless three-body phase space. -/
def masslessThreeBody (M : ℝ) : ℝ :=
  M ^ 2 / (128 * Real.pi ^ 3)

theorem masslessThreeBody_pos {M : ℝ} (hM : 0 < M) :
    0 < masslessThreeBody M := by
  unfold masslessThreeBody
  positivity

/-- **The massless three-body phase space factors through the two-body phase space.**
`Φ₃(M) = (1/(2π)) ∫₀^{M²} Φ₂² ds`, where `Φ₂ = 1/(8π)` is `MuonRate.two_body` /
`PolarMeasure.two_body_phase_space` and `s` is the (spectator) pair invariant mass — the
recursive phase-space factorization (review item A3). `M²` is the kinematic upper limit of `s`
for three massless daughters. -/
theorem masslessThreeBody_factorization (M : ℝ) :
    masslessThreeBody M =
      (1 / (2 * Real.pi)) * ∫ _s in (0 : ℝ)..(M ^ 2),
        (1 / (8 * Real.pi)) * (1 / (8 * Real.pi)) := by
  rw [intervalIntegral.integral_const]
  unfold masslessThreeBody
  simp only [sub_zero, smul_eq_mul]
  ring

/-- Three-body partial width from an operator entry. -/
def threeBodyRate (T : ℂ) (M : ℝ) : ℝ :=
  Complex.normSq T * masslessThreeBody M

theorem threeBodyRate_nonneg (T : ℂ) {M : ℝ} (hM : 0 < M) :
    0 ≤ threeBodyRate T M := by
  unfold threeBodyRate
  exact mul_nonneg (Complex.normSq_nonneg _) (masslessThreeBody_pos hM).le

end PMElementaryParticles.MultiBodyPhaseSpace
