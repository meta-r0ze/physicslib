# PersistenceMechanics — PM framework

Lean 4 proofs for the survival/hazard, Gibbs and selection framework used by
Papers I–VI.

- What is checked: [OVERVIEW.md](OVERVIEW.md) — module map and results.
- What remains: [TODO.md](TODO.md) — inputs and open items.

Build: Lean 4.34.1 with Mathlib pinned in `lake-manifest.json`.

```sh
lake exe cache get
./build.sh PersistenceMechanics
```

- **DecayChannel.** Shared six-pillar decay template: capacity, map, protocol, governor, toll, margin, plus the channel action in the exponent.

- **ChannelMeasure / MarginCorrection.** Finite channel weights/probabilities and a supplied margin correction interface, shared by all decay systems.

- **CoherentAction.** Phase-preserving and cost-attenuating sectors of the same operational action, with combined weight and quality factor.

- **EffectiveAction.** The physics `S−iΓt/2` amplitude form with PM operational cost, normalized so `|A|² = exp(−βS_cost)`.

- **InformationTransfer.** The three general transfer modes: boundary conduction, capacity promotion, coordinate jump, with a shared phase/cost channel.

- **Rates.** Use ExponentialFilter for survival under a time-dependent hazard.
  Use Rates for constant hazards, parallel rate sums and finite mean life.
  A finite mean life needs a positive rate. HazardForm derives the common
  cost-proportional hazard, and Decay.rate computes the six-pillar channel rate.

The three nested-system rules are upstream here: `CapacityPartitioning`,
`ReversibleEncoding` and `ImpedanceMatching`. Applications must supply work,
coarse descriptions, metadata, interface laws and reserves. The rules do not
select a depth or a unique allocation. See [the rule map](OVERVIEW.md).

The substrate-free `Accounting`, `Hierarchy`, `Service`, `TransferPersistence`
and `WorkSelection` modules also live here. Constant-backlog balance has one
proof in `CapacityPartitioning`; `Service` supplies repeating-cycle applications.
