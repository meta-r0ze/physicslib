import PMFlavor.PMNS

/-! **Geometric golden ratio.**

A regular pentagon has side `1` and diagonal `d`.  Ptolemy applied to four
consecutive vertices gives

```
d * d = 1 * 1 + 1 * d,
```

i.e. `d² = 1 + d`.  The root above one is the golden ratio.  The 600-cell
contains pentagons, so this is the 5-fold aperture used by the solar angle.
-/

noncomputable section
namespace PMFlavor.GoldenGeometry

open PMFlavor

/-- The positive pentagon-diagonal ratio is the golden ratio. -/
theorem pentagon_ratio_eq_phi {d : ℝ} (hd : 1 < d) (h : d ^ 2 = 1 + d) :
    d = FlavourPulls.φ := by
  have hsq : (2 * d - 1) ^ 2 = 5 := by nlinarith
  have hpos : 0 < 2 * d - 1 := by linarith
  have hroot : 2 * d - 1 = Real.sqrt 5 := by
    calc
      2 * d - 1 = Real.sqrt ((2 * d - 1) ^ 2) := (Real.sqrt_sq hpos.le).symm
      _ = Real.sqrt 5 := by rw [hsq]
  unfold FlavourPulls.φ
  linarith

/-- The pentagon aperture gives the solar squared sine. -/
theorem solar_sineSq_eq {d : ℝ} (hd : 1 < d) (h : d ^ 2 = 1 + d) :
    1 / (2 * d) = PMNS.sineSquared 0 := by
  rw [pentagon_ratio_eq_phi hd h]
  simp [PMNS.sineSquared]


end PMFlavor.GoldenGeometry
