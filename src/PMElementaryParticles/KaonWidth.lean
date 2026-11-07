import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.NeutronRate
import PMFlavor.CKM
import PMConstants.ElectroweakE8
import PMConstants.CurrentConstants
import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Comparison / structural.**

Two-body charged-kaon width:

```
Γ(K⁺ → μ⁺ν) = G_F² f_K² m_K m_μ² (1 − m_μ²/m_K²)² / (8π).
```

`f_K` is a supplied input; the E8 kaon decay constant is still open.
-/

noncomputable section
namespace PMElementaryParticles.KaonWidth

open PMElementaryParticles.LeptonMasses
open PMElementaryParticles.CompositeMasses
open PMElementaryParticles.NeutronRate

def kaonWidth (fK : ℝ) : ℝ :=
  fermiME ^ 2 * fK ^ 2 * kaonPlus * muon ^ 2 *
    (1 - (muon / kaonPlus) ^ 2) ^ 2 / (8 * Real.pi)

def kaonLifetime (fK : ℝ) : ℝ :=
  1 / kaonWidth fK

theorem kaonLifetime_eq (fK : ℝ) : kaonLifetime fK = 1 / kaonWidth fK := rfl

/-- Two-body width with the CKM factor `|Vus|²`. -/
def kaonWidthCKM (fK Vus : ℝ) : ℝ :=
  kaonWidth fK * Vus ^ 2

/-- E8 kaon decay constant `v/(Δ²−ν²) = v/1593`. -/
noncomputable def kaonDecayConstantE8 : ℝ :=
  PMConstants.ElectroweakE8.vev PMConstants.CurrentConstants.alpha 1 /
    (((PMSubstrate.E8Values.Delta : ℝ) ^ 2 - (PMSubstrate.E8Values.nu : ℝ) ^ 2))

/-- E8 `|Vus| = s₁₂ c₂₃`. -/
def vusE8 : ℝ := PMFlavor.CKM.s12 * PMFlavor.CKM.c23

/-- E8 kaon width. -/
noncomputable def kaonWidthE8 : ℝ :=
  kaonWidthCKM kaonDecayConstantE8 vusE8

/-- E8 kaon lifetime. -/
noncomputable def kaonLifetimeE8 : ℝ := 1 / kaonWidthE8

end PMElementaryParticles.KaonWidth
