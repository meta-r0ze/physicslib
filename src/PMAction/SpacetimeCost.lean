import PMAction.DefectGap
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# PM's cost on spacetime histories

**PM premise (Paper I, Capacity).** The cost of a configuration is local, measured from the vacuum
and relabeling-symmetric, so it counts distinctions between causally adjacent sites
(`PMSubstrate.Distinctions.only_distinctions_cost`). Paper I sets this in the **causal plane**:
"at speed one, one unit of boundary is one tick, so crossing one boundary edge is one
transition". A tick is a causal step like a spatial one. So a site whose state differs between
consecutive ticks is a distinction and costs one transition, exactly like a spatial boundary edge.
This file takes that reading as the definition of the cost of a history.

Setting: a spatial site graph `G` and `L + 1` ticks. The spacetime graph is the box product
`G □ path(L+1)`: two spacetime sites are adjacent when they are neighbours in space at the same
tick, or the same site at consecutive ticks. Sites are ordered lexicographically so that
`DefectGap` (which counts each boundary edge once) applies.

* `spacetime_adj`: adjacency is spatial-at-one-tick or temporal-at-one-site.
* `temporal_distinction`: a site that changes state between consecutive ticks contributes a
  boundary edge, so it costs one transition. This is the premise in formal form.
* `spacetime_connected`: spacetime is connected when space is.
* `spacetime_gap`: every non-uniform history costs at least one transition, for every spatial
  volume and every number of ticks.
* `spacetime_unique_vacuum`: the zero-cost histories are exactly the uniform ones.
* `history_weight`: at survival `p = e^{−β}` per transition, a history of cost `n` has weight
  `e^{−β n} = p^n`. So every boundary edge, spatial or temporal, carries the **same** activity
  `q = e^{−β}`. The per-contour activity is fixed by the single PM coupling, not supplied
  separately.
-/

namespace PMAction.SpacetimeCost
open SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (L : ℕ)

/-- Spacetime sites `(x, t)`, ordered lexicographically. -/
abbrev Site (V : Type*) (L : ℕ) := Lex (V × Fin (L + 1))

/-- The spacetime graph: space at one tick, or one site at consecutive ticks. -/
def spacetime : SimpleGraph (Site V L) := (G □ pathGraph (L + 1)).comap ofLex

omit [Fintype V] [LinearOrder V] in
theorem spacetime_adj (a b : Site V L) :
    (spacetime G L).Adj a b ↔
      (G.Adj (ofLex a).1 (ofLex b).1 ∧ (ofLex a).2 = (ofLex b).2) ∨
        ((pathGraph (L + 1)).Adj (ofLex a).2 (ofLex b).2 ∧ (ofLex a).1 = (ofLex b).1) := by
  simp [spacetime, boxProd_adj]

omit [Fintype V] [LinearOrder V] in
theorem spacetime_connected (hG : G.Connected) : (spacetime G L).Connected :=
  (Iso.comap ofLex (G □ pathGraph (L + 1))).connected_iff.mpr
    (hG.boxProd (pathGraph_connected L))

noncomputable instance : DecidableRel (spacetime G L).Adj := Classical.decRel _

/-- **Time-like distinctions cost.** If site `x` changes state between ticks `t` and `t + 1`, the
pair is a boundary edge of the history (in lexicographic orientation). -/
theorem temporal_distinction (σ : Site V L → Bool) (x : V) (t : Fin (L + 1)) (t' : Fin (L + 1))
    (htt : (t : ℕ) + 1 = t') (hflip : σ (toLex (x, t)) ≠ σ (toLex (x, t'))) :
    (toLex (x, t), toLex (x, t')) ∈ PMSubstrate.Distinctions.cutEdges (spacetime G L) σ := by
  have hadj : (spacetime G L).Adj (toLex (x, t)) (toLex (x, t')) := by
    rw [spacetime_adj]
    right
    refine ⟨?_, rfl⟩
    simp only [ofLex_toLex, pathGraph_adj]
    left; exact htt
  have hlt : toLex (x, t) < toLex (x, t') := by
    rw [Prod.Lex.toLex_lt_toLex]
    right
    exact ⟨rfl, show t < t' by rw [Fin.lt_def]; omega⟩
  simp [PMSubstrate.Distinctions.cutEdges, PMSubstrate.Distinctions.distinctions,
    PMSubstrate.Distinctions.pairs, hadj, hflip, hlt]

/-- **The spacetime gap.** Every non-uniform history costs at least one transition, whatever
the spatial volume and the number of ticks. -/
theorem spacetime_gap (hG : G.Connected) (σ : Site V L → Bool) (hσ : ¬ DefectGap.Uniform σ) :
    1 ≤ DefectGap.cost (spacetime G L) σ :=
  DefectGap.cost_ge_one (spacetime G L) (spacetime_connected G L hG) σ hσ

/-- **Unique spacetime vacuum.** -/
theorem spacetime_unique_vacuum (hG : G.Connected) (σ : Site V L → Bool) :
    DefectGap.cost (spacetime G L) σ = 0 ↔ DefectGap.Uniform σ :=
  DefectGap.cost_eq_zero_iff (spacetime G L) (spacetime_connected G L hG) σ

/-- **One activity for every boundary edge.** The weight of a history is `e^{−β·cost}`, which is
the per-transition survival `p = e^{−β}` raised to the number of boundary edges, spatial and
temporal alike. -/
theorem history_weight (β : ℝ) (σ : Site V L → Bool) :
    DefectGap.survival (spacetime G L) (Real.exp (-β)) σ =
      Real.exp (-β * (DefectGap.cost (spacetime G L) σ : ℝ)) :=
  DefectGap.survival_eq_gibbs (spacetime G L) β σ

end PMAction.SpacetimeCost
