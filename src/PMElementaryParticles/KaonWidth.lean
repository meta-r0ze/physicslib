import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.CompositeMasses
import PMElementaryParticles.NeutronRate
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

end PMElementaryParticles.KaonWidth
