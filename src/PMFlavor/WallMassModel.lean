import PMFlavor.WallDispersion
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Wall mass/momentum model

At momentum `p`, the branch impedance is

```
Z(p) = √(E(p,m_low) / E(p,m_high)).
```

At `p = 0` this is the mass ratio; as `p` grows it tends to one.  This competes
with the phase-coherence requirement, which needs enough momentum when the mass
gap exceeds `π/43`.
-/

noncomputable section
namespace PMFlavor.WallMassModel

open PMFlavor.WallDispersion

def wallImpedanceAt (p m0 m2 : ℝ) : ℝ :=
  Real.sqrt (wallEnergy p m0 / wallEnergy p m2)

end PMFlavor.WallMassModel
