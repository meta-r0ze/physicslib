import PMHadrons.EmissionScale
import PMSubstrate.PersistencePremises
import Mathlib.Tactic

/-! **Construction (step 1 of the emission space).**

# The pion's emission mode space as a set

`EmissionScale` writes `fπ = v/|Ω_π|` with the count `|Ω_π| = Δ² + Δ − χ = 1890` assigned. Here
`Ω_π` is a defined set and `1890` is its size:

* `cone` — the one-cycle causal cone `{(t, x) : t < Δ, |x| ≤ t}` (Margin's `Δ²`,
  `PersistencePremises.causal_cone_card`): the events from which a carrier can leave within one
  cycle.
* `survivingPhases` — the boundary phases of the `Δ`-cycle that survive the boundary gap `χ`
  (the Governor's `Δ − χ`, as in `PMAtoms.AlphaPersistence.survivingPhases` and
  `E8Margin.phaseMargin = (Δ−χ)/Δ`): the slots through which it can leave at the cycle boundary.
* `pionEmission = cone ⊔ survivingPhases`, with `pionEmission_card : |Ω_π| = pionModes = 1890`.

So the pion's count is Margin's cone plus the Governor's surviving phases, both already in the
substrate. The reading "emission = within-cycle cone + boundary survivors" is the modelling step.

**The kaon (step 2, open).** One rule must give both mesons, the only difference being the
kaon's line carrier (`StrangeCarrier`: a line-tier carrier holds the `σ`-direction register;
occupancy `χ` → `χ + σ`). The obvious substrate operations on this set, fixed before comparing
(counts by enumeration outside Lean; FLAG `fK/fπ = 1.1934(19)` needs `|Ω_K| ≈ 1581–1586`):

| rule (what the line carrier does) | `|Ω_K|` | `fK/fπ` |
|---|---:|---:|
| Protocol merges the orientation pair `x ↔ −x` on the cone | 987 | 1.915 |
| Governor gap grows from `χ` to `χ + σ` | 1885 | 1.003 |
| the carrier's own worldline `x = 0` leaves the cone | 1847 | 1.023 |
| the carrier's `σ` worldlines `|x| ≤ 2` leave the cone | 1681 | 1.124 |
| emission starts after `ν` steps (the cone minus its first `ν` slices) plus survivors | 1634 | 1.157 |
| the same delayed cone, no survivors (this is the assigned `Δ² − ν²`) | 1593 | 1.186 |

None reaches the window. The assigned kaon count does have a set reading — the cone with its first
`ν = 16` time slices removed, `|{ν ≤ t < Δ, |x| ≤ t}| = Δ² − ν²` — but it drops the surviving
boundary phases the pion keeps; applying the pion's rule consistently (delayed cone plus
survivors) moves `fK/fπ` further from the measurement. The missing premise is how a direction-holding carrier restricts the
one-cycle cone; the cone here is one spatial direction (`causal_cone_card`), so a rule that uses
the carrier's `σ` directions probably needs the cone in more than one direction.
-/

namespace PMHadrons.EmissionSpace
open Finset PMSubstrate.E8Values

/-- The one-cycle causal cone: events `(t, x)` with `t < Δ`, `|x| ≤ t`. -/
def cone : Finset (Σ _t : ℕ, ℤ) :=
  (range Delta).sigma (fun t => Icc (-(t : ℤ)) t)

/-- **The cone has `Δ²` events** (Margin's count). -/
theorem cone_card : cone.card = Delta ^ 2 := by
  unfold cone
  rw [card_sigma]
  exact PMSubstrate.PersistencePremises.causal_cone_card Delta

/-- Boundary phases of the `Δ`-cycle that survive the boundary gap `χ`. -/
def survivingPhases : Finset (Fin Delta) :=
  univ.filter (fun i => chi ≤ i.val)

/-- **`Δ − χ = 41` boundary phases survive** (the Governor's count). -/
theorem survivingPhases_card : survivingPhases.card = Delta - chi := by
  decide

/-- The pion's emission mode space: the cone and the surviving boundary phases. -/
def pionEmission : Finset ((Σ _t : ℕ, ℤ) ⊕ Fin Delta) :=
  cone.disjSum survivingPhases

/-- **`|Ω_π|` is the assigned pion count**, now the size of a defined set. -/
theorem pionEmission_card : pionEmission.card = EmissionScale.pionModes := by
  unfold pionEmission EmissionScale.pionModes
  rw [card_disjSum, cone_card, survivingPhases_card]

theorem pionEmission_card_eq : pionEmission.card = 1890 := by
  rw [pionEmission_card, EmissionScale.pionModes_eq]

end PMHadrons.EmissionSpace
