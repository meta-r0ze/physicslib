import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Generic decay channel

Shared by PMAtoms and PMElementaryParticles:

```
rate = β · c0 · capacity · margin · protocol · exp(−cost)
```
-/

noncomputable section
namespace PersistenceMechanics.Decay

structure DecayChannel where
  capacity : ℝ
  protocol : ℝ
  cost : ℝ
  margin : ℝ

def rate (β c0 : ℝ) (c : DecayChannel) : ℝ :=
  β * c0 * c.capacity * c.margin * c.protocol * Real.exp (-c.cost)

def lifetime (β c0 : ℝ) (c : DecayChannel) : ℝ :=
  1 / rate β c0 c

theorem rate_pos (β c0 : ℝ) (c : DecayChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hcap : 0 < c.capacity)
    (hmar : 0 < c.margin) (hpro : 0 < c.protocol) :
    0 < rate β c0 c := by
  unfold rate
  positivity

theorem lifetime_pos (β c0 : ℝ) (c : DecayChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hcap : 0 < c.capacity)
    (hmar : 0 < c.margin) (hpro : 0 < c.protocol) :
    0 < lifetime β c0 c := by
  unfold lifetime
  exact one_div_pos.mpr (rate_pos β c0 c hβ hc0 hcap hmar hpro)

def totalRate (β c0 : ℝ) (channels : List DecayChannel) : ℝ :=
  List.sum (channels.map (fun c => rate β c0 c))

def familyLifetime (β c0 : ℝ) (channels : List DecayChannel) : ℝ :=
  1 / totalRate β c0 channels

end PersistenceMechanics.Decay
