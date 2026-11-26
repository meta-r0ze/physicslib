import PMConstants.LinkCustodial

/-! **Interface correction `Δr`.**

The W/Z interface factor is `k`; the on-shell correction is

```
Δr = 1 - 1/k.
```

`LinkCustodial` already proves the Z-anchor window and decomposes the opposite-sign
term into a leading top-splitting piece plus a remainder.  This module names `Δr`
and records the decomposition without pretending the screening/remainder inputs
are derived.
-/

noncomputable section
namespace PMConstants.InterfaceCorrection

open PMConstants ElectroweakE8 CertifiedConstants GaugeSpectrum ElectroweakBounds

/-- On-shell interface correction. -/
def deltaR (k : ℝ) : ℝ := 1 - 1 / k

/-- The correction decomposes as screening minus the opposite-sign term. -/
theorem deltaR_decomposition {dα X k : ℝ}
    (hdec : 1 / k = 1 - dα + X) : deltaR k = dα - X := by
  unfold deltaR
  linarith

end PMConstants.InterfaceCorrection
