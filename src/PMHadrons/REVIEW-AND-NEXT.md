# PMHadrons — open work

Only work that remains, in priority order. Checked results are in
[`OVERVIEW.md`](OVERVIEW.md).

**The frame.** One elementary carrier is not yet a new system; several carriers persisting
together on E8 are. Two E8 quantities define such a composite: its **occupancy** (how much
substrate the persistent configuration holds → its mass) and its **emission overlap** (how
readily it sheds a carrier → its decay amplitude). Both are properties of one object — the
composite's persistent configuration — which is the single thing still missing. The
Standard-Model values below are comparison targets only, never inputs or mechanisms.

## 1. Occupancy: the minimum substrate a persistent composite holds — research

A composite costs `m = n·α⁻¹ + residual`: `n` substrate cells, each paying the full six-pillar
budget `α⁻¹` (so every held cell carries all six pillars), plus an interaction residual. The
reading under test is: **a carrier cohort is a new persistent system exactly when it holds at
least `n` cells; below that it has nowhere to stand and rearranges (decays).** Then `n` is the
minimum room needed, not a fitted number.

**Proved so far (`Occupancy`).** The minimum-room principle is formalized: every persistent
placement holds ≥ `n` cells and a placement below `n` is not persistent (`minOccupancy_le`,
`not_persistent_of_card_lt`); the meson ledgers are exactly the occupancy form
(`pionPlus_eq_occupancyMass`, `kaonPlus_eq_occupancyMass`); and a colour-neutral composite needs
≥ 2 carriers, hence ≥ `χ = 2` cells (`occupancy_ge_two_of_colourNeutral`) — the **pion's lower
bound is derived**. `tied_minimal_of_moved` gives the dichotomy: `n` is a result iff the
persistence predicate forces a unique least-occupancy placement.

**The kaon's extra `σ` now has a concrete candidate (`StrangeCarrier`).** `σ` is the **Protocol**
pillar's interaction-direction / embedding-address count (three spatial + two boundary): the
defect's embedding occupies `σ` of the `R_M` cycle addresses and Protocol routes among the
`R_M − σ = 167` residual ones (`PMSubstrate.TollFilters.residual_card`). The strange quark is a
**line-tier** carrier (`TierLedger.downTiers`), so under the premise "a line-tier carrier embeds
the `σ` directions" it holds `σ` addresses, giving `nK = χ + σ` while the point-tier pion keeps
`nπ = χ`. So the whole `n` reduces to the colour-singlet base plus line-tier direction counts.

**Still missing on E8.** The persistence predicate itself (what makes a multi-carrier placement
self-supporting); the single premise that a line-tier carrier spans the `σ` directions; and the
`Δ²`-based nucleon account.

**Tasks.**
1. State the **persistence/occupancy rule**: among the configurations of a carrier cohort,
   which hold enough cells to persist? The framework's test is
   `PersistenceMechanics.SelectionSymmetry.unique_minimizer_fixed` — a discrete option family
   plus a cost. If the least-occupancy persistent set is unique, `n` is derived.
2. A capacity derivation in the style of `PMConstants/VevLedger.slotCount = χΔ²−(ν+DΔ) = 3510`
   (a count already derived from capacity rather than fitted).
3. One account for the nucleon base `Δ²` and the meson cell budgets, or a stated reason they
   differ (`m_p/α⁻¹ ≈ 13.4` is not a whole number).

**Do not** integer-search for a rule matching `χ`, `σ+χ`: two points admit infinitely many rules,
so only a cost or a capacity argument makes one a derivation. The candidate `n = χ + σ·N_s`
(`N_s` = strange carriers) fits both but is not committed.

## 2. Emission overlap: how readily the composite sheds a carrier — construction, large

When a persistent composite rearranges it emits a single carrier (e.g. a lepton carrying away the
weak channel). That emission coupling is what the SM comparison calls the decay constant
`fπ`/`fK`; on E8 it is the **overlap of the composite configuration with the outgoing
single-carrier state, acted on by the substrate transition operator**. The current
`fπ = v/(Δ²+Δ−χ)`, `fK = v/(Δ²−ν²)` are assigned placeholders (`M`), and no cost selects them
(the standalone "one rule" framing is retired).

**Exists on E8.** carriers (`CarrierSpecies`), the transition operator
(`CarrierTransitionOperator`, `WeakTransition`), composite cohorts (`CompositeStates`), and an
overlap interface (`BoundStateOverlap`); `HadronicMatrixElement` is `⟨f|T|i⟩` for two
composites.

**Missing on E8.** the composite's configuration (a normalized many-carrier state, not just a
constituent list); a single-carrier emission operator; and the composite → one-carrier overlap.

**Tasks.**
1. **Single-occupancy test (cheap).** If item 1 gives a single cell/mode, compute the overlap as
   a finite sum and read off the emission coupling; compare to `v/1890`.
2. **Full configuration.** Build the composite mode explicitly and compute the overlap — this
   also yields the rearrangement amplitudes `K→ππ` and the `K_ℓ3` form factor `f₊(t)`.
3. **Consistency.** The SM rate form (`Γ ∝ G_F² f² m …`) and the measured `fπ`/`fK` are the
   comparison; the E8 emission coupling must reproduce them.

**Closes when** the emission overlap is computed from the composite configuration. Until then
`fπ`/`fK` stay declared model inputs (now shown in `e8p`, `f_k_mev` ≈ 3.8σ).

## Not work

The continuum neutron comparison (`NeutronRate`) is a labelled cross-check, not an E8
assumption; the E8-native route (`NeutronPrediction`) is the headline. No action.
