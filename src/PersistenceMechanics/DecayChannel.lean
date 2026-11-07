import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Generic six-pillar decay channel

The fields mirror the six persistence pillars:

```
capacity, map, protocol, governor, toll, margin
```

`action` is the channel's accumulated operational cost/barrier, not a seventh
pillar.  The rate is

```
rate = β · toll · capacity · map · protocol · governor · margin · exp(−action).
```

`governor` is a gate factor (typically `0` or `1`); `map` is the conserved-identity
overlap; `toll` is the per-transition `c0`; `margin` is the noise/attempt weight.
-/

noncomputable section
namespace PersistenceMechanics.Decay

structure DecayChannel where
  capacity : ℝ
  map : ℝ
  protocol : ℝ
  governor : ℝ
  toll : ℝ
  margin : ℝ
  action : ℝ

def rate (β : ℝ) (c : DecayChannel) : ℝ :=
  β * c.toll * c.capacity * c.map * c.protocol * c.governor * c.margin *
    Real.exp (-c.action)

def lifetime (β : ℝ) (c : DecayChannel) : ℝ :=
  1 / rate β c

theorem rate_pos (β : ℝ) (c : DecayChannel)
    (hβ : 0 < β) (hcap : 0 < c.capacity) (hmap : 0 < c.map)
    (hpro : 0 < c.protocol) (hgov : 0 < c.governor)
    (htoll : 0 < c.toll) (hmar : 0 < c.margin) :
    0 < rate β c := by
  unfold rate
  positivity

theorem lifetime_pos (β : ℝ) (c : DecayChannel)
    (hβ : 0 < β) (hcap : 0 < c.capacity) (hmap : 0 < c.map)
    (hpro : 0 < c.protocol) (hgov : 0 < c.governor)
    (htoll : 0 < c.toll) (hmar : 0 < c.margin) :
    0 < lifetime β c := by
  unfold lifetime
  exact one_div_pos.mpr (rate_pos β c hβ hcap hmap hpro hgov htoll hmar)

def totalRate (β : ℝ) (channels : List DecayChannel) : ℝ :=
  List.sum (channels.map (fun c => rate β c))

def familyLifetime (β : ℝ) (channels : List DecayChannel) : ℝ :=
  1 / totalRate β channels

/-- Physical lifetime from a tick duration and a per-tick rate. -/
def physicalLifetime (tick β : ℝ) (c : DecayChannel) : ℝ :=
  tick / rate β c

theorem physicalLifetime_eq (tick β : ℝ) (c : DecayChannel) :
    physicalLifetime tick β c = tick / rate β c := rfl

end PersistenceMechanics.Decay
