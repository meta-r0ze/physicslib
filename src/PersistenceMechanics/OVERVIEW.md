# Persistence Mechanics: Lean

| Module | Paper | Content |
|---|---|---|
| `ExponentialFilter` | §4.1 | `P(T) = exp(−∫h)` solves the hazard equation `P' = −hP`; cost-proportional hazard gives `exp(−βS)`; survival over consecutive intervals multiplies; the discrete filter `q^N = exp(−βS)` with `β = −ln q / c₀`. |
| `HazardForm` | §4.1 | The cost-proportional hazard with a common `β` is derived: if survival depends on a history only through its accumulated cost (one function `F` for all histories), survival over consecutive stretches multiplies, and more cost never raises survival, then `F(S) = exp(−βS)` for one `β ≥ 0` and the hazard is `βZ`. For integer (transition-count) cost the first two suffice. |
| `Selection` | §4.2–4.4 | Distribution conditional on survival, relative odds, **Proposition (Selection by Operational Action)** with `S_i(T) = s_i T + o(T)`, selection timescale `1/(βΔs)`. |
| `Gibbs` | §4.2 | Finite survival weights `exp(−βS)` at equal priors: positivity, ratios, ordering, a finite penalty never deletes a history; the β → ∞ limit concentrates uniformly on the minimum-cost histories. Moved from Paper II (`Survival`, `Concentration`). |
| `ChannelMeasure` | finite `ChannelMeasure`, `total`, `probability`, `probability_sum`, `probability_nonneg`, `subsetProbability`, `subsetProbability_nonneg`; channel-counting measure over an arbitrary finite label type. |
| `MarginCorrection` | supplied `correctedWeight`, `correctedRate`, positivity; substrate margin correction interface. |
| `InformationTransfer` | `TransferMode` (`inCycle`, `referenceWall`, `otherWall`), `TransferChannel`, amplitude/rate, admissibility; Paper IV transfer classification. |
| `EffectiveAction` | `amplitude = exp(iφ − (β/2)S_cost)`, `amplitude_normSq = exp(−βS_cost)`, `width = β·cost/time`, `decoherenceRate`; physics `S−iΓt/2` form. |
| `CoherentAction` | `phaseWeight = exp(iφ)`, `costWeight = exp(−βC)`, `combinedWeight`; phase has unit modulus, cost carries attenuation; `qualityFactor`. |
| `DecayChannel` | Shared six-pillar channel algebra: `capacity`, `map`, `protocol`, `governor`, `toll`, `margin`, plus `action`; `rate = β·toll·capacity·map·protocol·governor·margin·exp(−action)`; `lifetime`, `physicalLifetime`, `totalRate`, `familyLifetime`. |
| `LawSelection` | application | Candidate event laws on a finite label set: the uniform law uniquely minimizes the average return cost `−(1/|Ω|)Σ log p` and the worst-case cost `−log min p`, so it is the law that survives selection. Used by Paper I (`PersistenceMaximin`). |
| `SelectionSymmetry` | selection | A cost can only select its fixed points: `unique_minimizer_fixed` (an invariant cost with a unique minimizer fixes it) and `exists_tied_of_moved` (a moved point is tied). Framework shape for every open "model choice": a **discrete** symmetry with a uniqueness-forcing cost resolves a choice (`SectorExchange`); a **continuous** symmetry ties and needs a symmetry-breaking input (`ReferenceSelection`, the CP sign). |

Inputs, not theorems: the three premises of `HazardForm` (survival depends only on accumulated
cost, through one function for all histories; consecutive stretches multiply; more cost never
helps). The cost-proportional hazard and its common `β` are derived from them. Everything else
is proved. `Audit.lean` prints the axioms of the main results (only
`propext`, `Classical.choice`, `Quot.sound`).

Toolchain and Mathlib match the paper-series projects (Lean 4.34.1, Mathlib `d13f23b`). Build:
`./build.sh PersistenceMechanics`.

## Nested Rule 3: Impedance Matching

`ImpedanceMatching` states the interface rule of Nested Persistence for the
positive-real law: reflection `r = (Z_l − Z_s)/(Z_l + Z_s)`, transmission
`T = 1 − r²`, the conserved ledger `P r² + P T = P` (`ledger`), the reserve
criterion `P r² ≤ B ⇔ T ≥ 1 − B/P` (`admissible_iff_transmission`), and exact
matching under zero reserve (`zero_reserve_matched`). It is a budget condition,
not an optimality claim. The K-Automaton instance is
`PMElementaryParticles.ImpedanceLedger`. (Written, awaiting a compile check.)

## Nested Rule 2: Reversible Encoding

`ReversibleEncoding` states the encoding rule. A coarse description `q` plus
metadata `m` is reversible exactly when `m` separates every fibre of `q`
(`encode_injective_iff`). Then fibres have at most `|M|` states
(`fiber_card_le`) and `|X| ≤ |Q|·|M|` (`card_le_mul`). For site data, the
reference value with the differences from it is reversible
(`relational_injective`), and dropping the reference merges exactly the global
shifts (`differences_eq_iff`). The protocol-record instance is
`PMElementaryParticles.RecordEncoding`. (Written, awaiting a compile check.)

## Nested Rule 1: Capacity Partitioning

`CapacityPartitioning` states the partition rule. A feasible allocation serves
every task and fits every subsystem, so `∑ w + ∑ h ≤ ∑ C` (`global_budget`). With
equal capacity the subsystem count is at least `(∑ w + ∑ h)/C`
(`count_lower_bound`). Over a repeating cycle, bounded backlog forces zero drift,
so service balances demand (`bounded_backlog_zero_drift`, `service_balance`). The
clock-ring instance is `PMElementaryParticles.CapacityLedger`. (Written, awaiting a
compile check.)
