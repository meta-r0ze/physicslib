import PMAction.WallDispersion
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

end PMFlavor.WallMassRatio
