import PMFlavor.BreakingLink
import PersistenceMechanics.CoherentAction
import PMFlavor.MixingMatrix

/-! **Experimental/candidate module.**

# Broken-link phase and cost

The broken-link parameters are interpreted as:

```
δ = phase mismatch of the wall link
ε = attenuation/cost of the wall link
```

The amplitude is `exp(iδ − (β/2)ε)`.  Numerical values of `δ, ε` remain physical
wall inputs.
-/

noncomputable section
namespace PMFlavor.BreakingWall

open PMFlavor.BreakingLink
open PersistenceMechanics.CoherentAction

structure BreakingPhase where
  delta : ℝ
  epsilon : ℝ

/-- Broken link from the phase mismatch. -/
def brokenLinkOfPhase (w : BreakingPhase) : Matrix (Fin 3) (Fin 3) ℂ :=
  brokenLink w.delta

/-- Coherent/incoherent wall amplitude. -/
def wallAmplitude (β : ℝ) (w : BreakingPhase) : ℂ :=
  combinedWeight w.delta β w.epsilon


/-- The exceptional mixing curve in phase/cost variables. -/
def ExceptionalWall (w : BreakingPhase) : Prop :=
  w.delta = PMFlavor.MixingMatrix.rootMInv
    (5 - PMFlavor.MixingMatrix.rootM w.epsilon)

/-- The physical wall point must lie off the exceptional curve. -/
def PhysicalWallInput (w : BreakingPhase) : Prop := ¬ ExceptionalWall w

end PMFlavor.BreakingWall
