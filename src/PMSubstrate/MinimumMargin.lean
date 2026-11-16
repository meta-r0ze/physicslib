import PMSubstrate.Pillars

/-!
# The minimum margin is the disturbance over the correction gain

`Pillars.map_maintains`: a state corrected toward its retained reference `r` with gain `k ∈ (0, 1]`,
under disturbances bounded by `W`, stays within `max |x₀ − r| (W/k)` of `r`. `Pillars.margin_iff`:
Margin is the distance to the non-viable set. Together:

* `persists_of_margin`: if the viable set contains every state within `m` of `r` and
  `m > max |x₀ − r| (W/k)`, the state stays viable at every tick.
* So, started at the reference, the minimum margin to continue to persist is `W/k`: the disturbance
  per tick over the correction gain. Map (the correction toward `r`) and Margin (the room around
  `r`) meet in that one quotient.

**On the wire** (PMElementaryParticles REVIEW). A protocol's margin, measured in units of the
disturbance it suffers per tick, is `1/k`, the inverse of its correction gain. With the spinor
carrier's flip as the disturbance, the margins read from the masses (`δ_O/k_f` = `64.6` down, `18.8` `e`,
`11.2` up) are correction gains `0.0155`, `0.053`, `0.089`. What sets a protocol's correction gain is the
open question; this module only fixes the form.
-/

namespace PMSubstrate.MinimumMargin
open PMSubstrate.Pillars

/-- **A margin larger than the Map's deviation bound keeps the state viable.** -/
theorem persists_of_margin {x w : ℕ → ℝ} {r k W m : ℝ} {V : Set ℝ}
    (hk0 : 0 < k) (hk1 : k ≤ 1) (hw : ∀ t, |w t| ≤ W)
    (h : ∀ t, x (t + 1) = x t - k * (x t - r) + w t)
    (hV : ∀ y, |y - r| < m → y ∈ V) (hm : max |x 0 - r| (W / k) < m) :
    ∀ t, x t ∈ V := by
  intro t
  exact hV _ (lt_of_le_of_lt (map_maintains hk0 hk1 hw h t) hm)

end PMSubstrate.MinimumMargin
