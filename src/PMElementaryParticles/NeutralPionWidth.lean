import PMElementaryParticles.PionWidth
import PMElementaryParticles.CompositeMasses
import PMConstants.CurrentConstants
import Mathlib.Tactic

/-! **Comparison / E8-input check.**

Neutral-pion two-photon width:

```
Γ(π⁰ → γγ) = α² m_π⁰³ / (128π³ fπ²)
```

The factor `128 = 2·64` is the identical-photon 1/2.  `α`, `m_π⁰`, and `fπ`
are E8 inputs.
-/

noncomputable section
namespace PMElementaryParticles.NeutralPionWidth

open PMElementaryParticles.PionWidth
open PMElementaryParticles.CompositeMasses

/-- E8-input neutral-pion width. -/
noncomputable def neutralPionWidthE8 : ℝ :=
  (PMConstants.CurrentConstants.alpha ^ 2 * pion0 ^ 3) /
    (128 * Real.pi ^ 3 * pionDecayConstantE8 ^ 2)

/-- E8-input neutral-pion lifetime. -/
noncomputable def neutralPionLifetimeE8 : ℝ :=
  1 / neutralPionWidthE8

end PMElementaryParticles.NeutralPionWidth
