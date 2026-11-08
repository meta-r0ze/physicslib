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

/-- The Z-anchor requirement fixes `Δr` to the on-shell window. -/
theorem deltaR_window {k : ℝ} (hk : 0 < k)
    (hz : k * zMassSquared α electronGeV = ScaleConsistency.zAnchor ^ 2) :
    0.0349 < deltaR k ∧ deltaR k < 0.0353 := by
  simpa [deltaR] using LinkCustodial.delta_r_window hk hz

/-- The correction decomposes as screening minus the opposite-sign term. -/
theorem deltaR_decomposition {dα X k : ℝ}
    (hdec : 1 / k = 1 - dα + X) : deltaR k = dα - X := by
  unfold deltaR
  linarith

/-- With the leading top-splitting term, the non-leading remainder is bounded. -/
theorem deltaR_remainder {dα k X mt R : ℝ}
    (h : 0.0589 < dα ∧ dα < 0.0591) (hk : 0 < k)
    (hz : k * zMassSquared α electronGeV = ScaleConsistency.zAnchor ^ 2)
    (hdec : 1 / k = 1 - dα + X) (hmt : 172.28 < mt ∧ mt < 172.86)
    (hX : X = LinkCustodial.leadingTerm clockRatio (fermi α electronGeV) mt - R) :
    0.0082 < R ∧ R < 0.0091 :=
  LinkCustodial.remainder_required h hk hz hdec hmt hX

end PMConstants.InterfaceCorrection
