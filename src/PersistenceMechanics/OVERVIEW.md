# Persistence Mechanics: Lean

| Module | Paper | Content |
|---|---|---|
| `ExponentialFilter` | §4.1 | `P(T) = exp(−∫h)` solves the hazard equation `P' = −hP`; cost-proportional hazard gives `exp(−βS)`; survival over consecutive intervals multiplies; the discrete filter `q^N = exp(−βS)` with `β = −ln q / c₀`. |
| `HazardForm` | §4.1 | The cost-proportional hazard with a common `β` is derived: if survival depends on a history only through its accumulated cost (one function `F` for all histories), survival over consecutive stretches multiplies, and more cost never raises survival, then `F(S) = exp(−βS)` for one `β ≥ 0` and the hazard is `βZ`. For integer (transition-count) cost the first two suffice. |
| `Selection` | §4.2–4.4 | Distribution conditional on survival, relative odds, **Proposition (Selection by Operational Action)** with `S_i(T) = s_i T + o(T)`, selection timescale `1/(βΔs)`. |
| `Gibbs` | §4.2 | Finite survival weights `exp(−βS)` at equal priors: positivity, ratios, ordering, a finite penalty never deletes a history; the β → ∞ limit concentrates uniformly on the minimum-cost histories. Moved from Paper II (`Survival`, `Concentration`). |
| `ChannelMeasure` | finite `ChannelMeasure`, `total`, `probability`, `probability_sum`, `probability_nonneg`, `subsetProbability`, `subsetProbability_nonneg`; channel-counting measure over an arbitrary finite label type. |
| `MarginCorrection` | supplied `correctedWeight`, `correctedRate`, positivity; substrate margin correction interface. |
| `InformationTransfer` | `TransferMode` (`boundaryConduction`, `capacityPromotion`, `coordinateJump`), `TransferChannel`, amplitude/rate, admissibility; Paper IV transfer classification. |
| `EffectiveAction` | `amplitude = exp(iφ − (β/2)S_cost)`, `amplitude_normSq = exp(−βS_cost)`, `width = β·cost/time`, `decoherenceRate`; physics `S−iΓt/2` form. |
| `CoherentAction` | `phaseWeight = exp(iφ)`, `costWeight = exp(−βC)`, `combinedWeight`; phase has unit modulus, cost carries attenuation; `qualityFactor`. |
| `DecayChannel` | Shared six-pillar channel algebra: `capacity`, `map`, `protocol`, `governor`, `toll`, `margin`, plus `action`; `rate = β·toll·capacity·map·protocol·governor·margin·exp(−action)`; `lifetime`, `physicalLifetime`, `totalRate`, `familyLifetime`. |
| `LawSelection` | application | Candidate event laws on a finite label set: the uniform law uniquely minimizes the average return cost `−(1/|Ω|)Σ log p` and the worst-case cost `−log min p`, so it is the law that survives selection. Used by Paper I (`PersistenceMaximin`). |

Inputs, not theorems: the three premises of `HazardForm` (survival depends only on accumulated
cost, through one function for all histories; consecutive stretches multiply; more cost never
helps). The cost-proportional hazard and its common `β` are derived from them. Everything else
is proved. `Audit.lean` prints the axioms of the main results (only
`propext`, `Classical.choice`, `Quot.sound`).

Toolchain and Mathlib match the paper-series projects (Lean 4.34.1, Mathlib `d13f23b`). Build:
`./build.sh PersistenceMechanics`.
