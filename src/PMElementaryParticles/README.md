# PMElementaryParticles — Paper V decay library

Lean 4 proofs for *Persistence Mechanics V: Decay as a Conditional Routing Model*.
Paper V applies Paper II's shared dynamics to an **elementary-particle decay**
example: elementary-particle protocols on the E8 substrate, and their conditional
decay rates. It builds on PMSubstrate, PMAction and PMConstants. PMFlavor comes after
it: flavour is the label change of a charged-current event that changes protocol, so
it needs the protocols first. Library order: PMSubstrate → PMAction → PMConstants → PMKAutomaton → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`).

The [KAutomaton closeout](../PMKAutomaton/COMPONENTS.md#kautomaton-closeout)
gives the upstream contract. The [EP review](TODO.md#everything-else-still-open)
maps the admitted path, timing, readout and Toll inputs needed for
a physical species claim.

## Main results

- **The `192π³` is not an input.** `MuonRate.muon_rate` derives the massless
  muon width `Γ = G_F² m⁵/(192π³)` from the V−A contact amplitude
  `64 G²(p·k̄)(p_e·k)`, the covariant neutrino-pair integral and the massless
  phase-space measure.
- **Massive daughter, closed form.** `MassiveWidth.closed_width` evaluates the
  massive-daughter contact width
  `Γ = G²m⁵/(192π³)·[1 − 8r + 8r³ − r⁴ − 12r² log r]`, `r=(μ/m)²`, with exact
  massless/threshold endpoints.
- **From W exchange.** `WExchangeRate` (via Paper II `WeakVertex`) derives the
  contact amplitude as the zero-momentum-transfer limit of `W` exchange.
- **Decay law.** `DecayLaw` ties Paper I's survival law to a constant per-tick
  cost, with a finite-tick exponential and its continuum limit.
- **Protocol inventory.** `ProtocolInventory` proves the paper's 16-channel
  routing model: four base protocols (up 6, down 6, electron 2, neutrino 1), one
  sterile vacancy, two routing modes, and charge classes matching Paper III.
- **Protocol dynamics.** `ProtocolDynamics` models decay as a routing change on
  the inventory: charge-conserving exit cohorts, strictly lower tiers, finite
  descent (`no_infinite_chain`), and the muon `e+ν+ν̄` example.
- **Substrate existence.** `SubstrateLedger.substrate_has_components` shows the E8
  substrate actually contains each object the paper identifies (chiral grading,
  colour structure, charge spectrum, four protocols, sterile vacancy, tier ladder).
- **Phase-space start.** `PhaseSpace.solidAngle_one` derives the `4π` angular
  weight from the direction integral (first step of the measure construction).
- **Routing caveats.** `ProtocolCaveats` proves the paper's caveats: lower latency
  need not be reachable, and routing alone doesn't force stability.
- **Label changes and CP** (the CKM and PMNS readouts) are PMFlavor's, applied after this library.

## The six pillars on the wire

A protocol carried over the wire is a Persistence Mechanics system, and the flavour work is that
system's six pillars (`PersistenceMechanics`, Paper I: Finiteness gives Capacity and Margin,
Conservation gives Map and Protocol, Causality gives Toll and Governor):

| Pillar | On the wire | Library |
|---|---|---|
| Capacity | the three label states; the node's conductance | `PMAction.GenerationSector`, `KronSeries` |
| Margin | the other wall's detuning `δ_O` (a wall with no detuning is PM's "no margin, fragility": `PMAction.UndetunedWall`) | open: its size per protocol |
| Map | label states → the protocol's persisting states: the rotation `U` | open: derived per protocol from Margin (`PMAction.WireMass`) |
| Protocol | up, down, `e`, `ν` as information over the wire | `PMConstants.CarrierRepresentation` |
| Toll | node passage `α`; the three transfers are PM's three modes (`PersistenceMechanics.InformationTransfer`) | `NodeAmplitude`, `TransferAmplitude` |
| Governor | the stationary reference (`δ_R = 0`) and the weak refresh | `PMAction.ReferenceDetuning`, `CarrierActions` |

Most physics frameworks carry Capacity, Map, Protocol and Governor and leave Toll or Margin out; here
Toll is derived and Margin is the open number. Fill in Margin, and Map follows.

## Where to look

- **[OVERVIEW.md](OVERVIEW.md)** — the single map of what is proved and reusable
  (module-by-module) and what remains a physical input. **Start here to find a
  theorem you can use.**
- **[GENERATIONS.md](GENERATIONS.md)** compares glue addresses, wire routes and tier assignments.
- **[TODO.md](TODO.md)** — the remaining work, split into
  **mathematical proof gaps fillable in Lean** and **physical model inputs**.
- The paper source is under `../../paper/`.

## Sibling libraries

`PMHadrons` builds on this library: [README](../PMHadrons/README.md), [OVERVIEW](../PMHadrons/OVERVIEW.md), [TODO](../PMHadrons/TODO.md).
`PMAtoms` is a separate library in the same package: [README](../PMAtoms/README.md), [OVERVIEW](../PMAtoms/OVERVIEW.md), [TODO](../PMAtoms/TODO.md).

## Build and audit

Lean 4.34.1; the whole tree is one Lake package with `PMSubstrate` and `PMConstants`
already in this repository (see `AGENTS.md`). Then:

```sh
source ~/.elan/env
./build.sh PMElementaryParticles
```

`build.sh PMElementaryParticles` builds the `PMElementaryParticles` library, strictly audits transitive axioms against
`propext`, `Classical.choice`, `Quot.sound`, and rejects Paper VI imports. A
successful audit certifies the statements under their hypotheses; it does **not**
select the physical interaction, measure normalization or coupling.

## Verification

Run `./build.sh PMElementaryParticles`. No Paper VI imports; permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
