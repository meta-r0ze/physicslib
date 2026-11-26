import PersistenceMechanics.Rates
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

def lifetime (β : ℝ) (c : DecayChannel) (h : 0 < rate β c) : ℝ :=
  Rates.meanLife (rate β c) h

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
    0 < lifetime β c (rate_pos β c hβ hcap hmap hpro hgov htoll hmar) :=
  Rates.meanLife_pos (rate_pos β c hβ hcap hmap hpro hgov htoll hmar)

def totalRate (β : ℝ) (channels : List DecayChannel) : ℝ :=
  Rates.parallelRate (channels.map (rate β))

def familyLifetime (β : ℝ) (channels : List DecayChannel)
    (h : 0 < totalRate β channels) : ℝ :=
  Rates.meanLife (totalRate β channels) h

/-- Physical lifetime from a tick duration and a per-tick rate. -/
def physicalLifetime (tick β : ℝ) (c : DecayChannel) (h : 0 < rate β c) : ℝ :=
  tick * lifetime β c h

theorem physicalLifetime_eq (tick β : ℝ) (c : DecayChannel) (h : 0 < rate β c) :
    physicalLifetime tick β c h = tick / rate β c := by
  simp [physicalLifetime, lifetime, Rates.meanLife, div_eq_mul_inv]

end PersistenceMechanics.Decay
