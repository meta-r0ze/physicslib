import PMElementaryParticles.CompositePhaseSpace

/-! **Massless three-body phase space.**

For three massless daughters,

```
Φ₃ = M² / (128π³).
```

This is the massless coefficient; massive multi-body phase space remains a
kinematic integral and is not constructed here.
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

/-- Three-body partial width from an operator entry. -/
def threeBodyRate (T : ℂ) (M : ℝ) : ℝ :=
  Complex.normSq T * masslessThreeBody M

theorem threeBodyRate_nonneg (T : ℂ) {M : ℝ} (hM : 0 < M) :
    0 ≤ threeBodyRate T M := by
  unfold threeBodyRate
  exact mul_nonneg (Complex.normSq_nonneg _) (masslessThreeBody_pos hM).le

end PMElementaryParticles.MultiBodyPhaseSpace
