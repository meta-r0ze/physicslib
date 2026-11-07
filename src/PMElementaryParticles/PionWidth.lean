import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.NeutronRate
import PMConstants.ElectroweakE8
import PMConstants.CurrentConstants
import PMSubstrate.E8Values
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! **Comparison / structural.**

Two-body charged-pion width:

```
Γ(π⁺ → μ⁺ν) = G_F² f_π² m_π m_μ² (1 − m_μ²/m_π²)² / (8π).
```

The pion decay constant `f_π` is still a supplied input.
-/

noncomputable section
namespace PMElementaryParticles.PionWidth

open PMElementaryParticles.LeptonMasses
open PMElementaryParticles.NeutronRate

def pionWidth (fPi : ℝ) : ℝ :=
  fermiME ^ 2 * fPi ^ 2 * pionPlus * muon ^ 2 *
    (1 - (muon / pionPlus) ^ 2) ^ 2 / (8 * Real.pi)

def pionLifetime (fPi : ℝ) : ℝ :=
  1 / pionWidth fPi

theorem pionLifetime_eq (fPi : ℝ) : pionLifetime fPi = 1 / pionWidth fPi := rfl

/-- E8 pion decay constant in `m_e` units:
`v/(Δ² + Δ − χ)` with `m_e = 1`. -/
noncomputable def pionDecayConstantE8 : ℝ :=
  PMConstants.ElectroweakE8.vev PMConstants.CurrentConstants.alpha 1 /
    (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 +
      ((PMSubstrate.E8Values.Delta - PMSubstrate.E8Values.chi : Nat) : ℝ)))

/-- E8 pion width. -/
noncomputable def pionWidthE8 : ℝ := pionWidth pionDecayConstantE8

/-- E8 pion lifetime. -/
noncomputable def pionLifetimeE8 : ℝ := pionLifetime pionDecayConstantE8

end PMElementaryParticles.PionWidth
