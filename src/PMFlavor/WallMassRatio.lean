import PMAction.WallDispersion
import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Wall coupling ratio from the capacity impedance

If the wall mass ratio is the E8 capacity ratio

```
massSqM / massSqP = (16/21)² = 256/441,
```

then the wall couplings satisfy

```
y² = (25/336) δ²,   i.e. y/δ = 5/√336.
```
-/

noncomputable section
namespace PMFlavor.WallMassRatio

open PMAction.WallDispersion

theorem wall_coupling_ratio_of_mass_ratio (δ y : ℝ) (hδ : δ ≠ 0)
    (h : massSqM δ y / massSqP δ y = 256 / 441) :
    y ^ 2 = (25 / 336) * δ ^ 2 := by
  have hy : y ≠ 0 := by
    intro hy0
    subst y
    simp [massSqM, massSqP, rhoM, rhoP, rr] at h
    field_simp [hδ] at h
    norm_num at h
  obtain ⟨hprod, hsum, hPpos, hMnonneg⟩ := branch_masses δ y hy
  have hPne : massSqP δ y ≠ 0 := ne_of_gt hPpos
  have hM : massSqM δ y = (256 / 441) * massSqP δ y := by
    field_simp [hPne] at h ⊢
    linarith
  have hP : massSqP δ y = (21 / 16) * δ ^ 2 := by
    have hprod' : massSqP δ y * ((256 / 441) * massSqP δ y) = δ ^ 4 := by
      rw [← hM]; exact hprod
    have hδ2 : 0 < δ ^ 2 := by positivity
    nlinarith [hPpos, hδ2, hprod']
  have hM' : massSqM δ y = (16 / 21) * δ ^ 2 := by
    rw [hM, hP]; ring
  have hsum' : (21 / 16) * δ ^ 2 + (16 / 21) * δ ^ 2 = y ^ 2 + 2 * δ ^ 2 := by
    rw [← hP, ← hM', hsum]
  nlinarith

/-! ## The two ratios are substrate expressions

The mass ratio `256/441 = (16/21)²` is the capacity-basin ratio `(ν/(ν+σ))²`, and
the coupling ratio `25/336 = σ²/(ν(ν+σ))`. Neither is an independent choice. -/

theorem capacity_ratio_sq :
    (256 / 441 : ℝ) =
      (((PMSubstrate.E8Values.nu : ℝ) /
        (PMSubstrate.E8Values.nu + PMSubstrate.E8Values.sigma)) ^ 2) := by
  rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq]
  norm_num

theorem coupling_ratio :
    (25 / 336 : ℝ) =
      ((PMSubstrate.E8Values.sigma : ℝ) ^ 2 /
        ((PMSubstrate.E8Values.nu : ℝ) *
          (PMSubstrate.E8Values.nu + PMSubstrate.E8Values.sigma))) := by
  rw [PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.sigma_eq]
  norm_num

/-- The capacity mass-ratio hypothesis and the coupling ratio, both written as
substrate expressions: if `m_M²/m_P² = (ν/(ν+σ))²` then `y² = σ²/(ν(ν+σ)) δ²`. -/
theorem wall_coupling_ratio_substrate (δ y : ℝ) (hδ : δ ≠ 0)
    (h : massSqM δ y / massSqP δ y =
      (((PMSubstrate.E8Values.nu : ℝ) /
        (PMSubstrate.E8Values.nu + PMSubstrate.E8Values.sigma)) ^ 2)) :
    y ^ 2 =
      ((PMSubstrate.E8Values.sigma : ℝ) ^ 2 /
        ((PMSubstrate.E8Values.nu : ℝ) *
          (PMSubstrate.E8Values.nu + PMSubstrate.E8Values.sigma))) * δ ^ 2 := by
  have h' : massSqM δ y / massSqP δ y = (256 / 441 : ℝ) := by
    rw [h, capacity_ratio_sq]
  have h2 := wall_coupling_ratio_of_mass_ratio δ y hδ h'
  rw [coupling_ratio] at h2
  exact h2

end PMFlavor.WallMassRatio
