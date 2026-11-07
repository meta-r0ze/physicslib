import PMAtoms.MeanLife
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Generic E8 decay channel

All decay channels use the same finite-channel template:

```
rate = β · c0 · capacity · margin · protocol · exp(−cost)
```

Beta, alpha, fission and particle channels are instances.  This module fixes the
common algebra and positivity.
-/

noncomputable section
namespace PMAtoms

/-- A generic E8 decay channel. -/
structure DecayChannel where
  capacity : ℝ
  protocol : ℝ
  cost : ℝ
  margin : ℝ

/-- Channel rate from the common persistence template. -/
def DecayChannel.rate (β c0 : ℝ) (c : DecayChannel) : ℝ :=
  β * c0 * c.capacity * c.margin * c.protocol * Real.exp (-c.cost)

/-- Channel lifetime. -/
def DecayChannel.lifetime (β c0 : ℝ) (c : DecayChannel) : ℝ :=
  MeanLife (c.rate β c0)

theorem DecayChannel.rate_pos (β c0 : ℝ) (c : DecayChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hcap : 0 < c.capacity)
    (hmar : 0 < c.margin) (hpro : 0 < c.protocol) :
    0 < c.rate β c0 := by
  unfold DecayChannel.rate
  positivity

theorem DecayChannel.lifetime_pos (β c0 : ℝ) (c : DecayChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hcap : 0 < c.capacity)
    (hmar : 0 < c.margin) (hpro : 0 < c.protocol) :
    0 < c.lifetime β c0 :=
  MeanLife_pos (DecayChannel.rate_pos β c0 c hβ hc0 hcap hmar hpro)

/-- Total rate of a finite channel family. -/
def totalChannelRate (β c0 : ℝ) (channels : List DecayChannel) : ℝ :=
  List.sum (channels.map (fun c => c.rate β c0))

/-- Lifetime of a finite channel family. -/
def familyLifetime (β c0 : ℝ) (channels : List DecayChannel) : ℝ :=
  MeanLife (totalChannelRate β c0 channels)

end PMAtoms
