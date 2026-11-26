# PMFlavor — Paper IV: label changes in a charged-current event on E8

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum IV: Information Transfer*.

**What flavour is here** (ASD-STE100):
- The wire carries information. The wire has three label states. A label state is the glue class
  that the two walls do not use. The label is a property of the wire (PMAction).
- Movement along the wire does not change the label.
- A protocol is the type of information on the wire (up, down, electron, neutrino). Protocols are in
  PMElementaryParticles.
- A charged-current event changes the protocol. The event acts on one wall only. Thus the event can
  also change the label.
- "Flavour" is the label. "Flavour change" is a label change during an event.
- The in-cycle label change is `2 → 1`. The weak refresh keeps the label.
  `InCycleEvent` gives an E8 root word for the change with a supplied wall
  record. Its firing law and amplitude are open.
- A change to or from label `0` needs a spinor carrier. Only the reference node supplies it. Thus these
  two changes are small.
- `J` is the matrix of label-change amplitudes for one event. There are two: one for carriers off the
  reference axis (read out as the CKM) and one for carriers on it (read out as the PMNS).
- A state that persists has one frequency and one mass. If the persisting states are the label states,
  the observed matrix is `J`. The wire turns them a small quantity away, so in general it is
  `U_uᴴ J U_d`: `J` from PMFlavor, `U` from the wire (PMAction) and the protocols (PMElementaryParticles).

PMFlavor is not a model of Standard Model flavour. Every number comes from E8 structure or a narrowly
stated premise; measured values enter only as the final test in e8p.

## The six pillars on the wire

A protocol carried over the wire is a Persistence Mechanics system, and the flavour work is that
system's six pillars (`PersistenceMechanics`, Paper I: Finiteness gives Capacity and Margin,
Conservation gives Map and Protocol, Causality gives Toll and Governor):

| Pillar | On the wire | Library |
|---|---|---|
| Capacity | the three label states; the node's conductance | `PMAction.GenerationSector`, `KronSeries` |
| Margin | the other wall's detuning `δ_O` (a wall with no detuning is PM's "no margin, fragility": `PMAction.UndetunedWall`) | open: its size per protocol |
| Map | label states → the protocol's persisting states: the rotation `U` | open: derived per protocol from Margin (`PMAction.DetunedWire`) |
| Protocol | up, down, `e`, `ν` as information over the wire | `PMConstants.CarrierRepresentation` |
| Toll | node passage `α`; the three transfers are PM's three modes (`PersistenceMechanics.InformationTransfer`) | `NodeAmplitude`, `TransferAmplitude` |
| Governor | the stationary reference (`δ_R = 0`) and the weak refresh | `PMAction.ReferenceDetuning`, `CarrierActions` |

Most physics frameworks carry Capacity, Map, Protocol and Governor and leave Toll or Margin out; here
Toll is derived and Margin is the open number. Fill in Margin, and Map follows.

## Terminology

| Term | Meaning | Where |
|---|---|---|
| wire | the two-wall operator, its label states, its light-mass form | PMAction (`GenerationWalls`, `ReferenceWallFactorization`, `NativeFlavourWall`) |
| label state | the glue class a two-wall state omits (`Fin 3`); class `0` is the reference's (vector) class | `PMAction.GenerationLabel`, `GenerationWalls` |
| protocol | the type of information on the wire | `PMElementaryParticles.ProtocolInventory` |
| event | a charged-current event: the weak refresh on the reference's wall | `PMConstants.CarrierActions.weak`, `PMAction.WallChiralCurrent` |
| label change | what an event does to the label: one single-wall carrier plus one glue move | `PMAction.GenerationCurrent`, `EventTransfer` |
| `J` | label-change matrix of one event | `EventTransfer.J` |
| in-cycle / node change | the change uses the weak carrier's own class (stays in the cycle) / a spinor class (through the reference node) | `TransferGraph.inCycle_iff` |
| on / off the reference axis | where a carrier sits relative to axis `0`; fixes the readout (one leg, probability / two legs, amplitude) | `CarrierRepresentation.lepton_axis_split`, `NodeElimination` |
| `U` | persistence rotation of a protocol: persisting states versus label states | PMAction (`ReferenceWallFactorization`), PMElementaryParticles |

The three label changes (`EventTransfer.entry_of_class`, `TransferGraph`):

| Carrier class | Change | Kind | Read out off / on the axis |
|---|---|---|---|
| `0` (vector, the weak carrier) | `2 → 1` | in-cycle | `s₁₂` / `sin²θ₁₂` |
| `2` (spinor) | `1 → 0` | node, class on the reference's wall in label `0` | `\|V_cb\|` / `sin²θ₂₃` |
| `1` (spinor) | `0 → 2` | node, class on the other wall in label `0` | `\|V_ub\| = s₁₃` / `sin²θ₁₃` |

Naming label `1` the second and `2` the first is the wall-naming convention; the wire's masses, with
the carriers placed by glue arithmetic (`PMAction.DetunedWire`), give the same names. The names conduction,
promotion and jump (`TransferGraph.mode`) are a candidate reading; they rest on one premise (the
reference-wall crossing is one step). Older modules and parts of the OVERVIEW say "generation" for a
label state.

## Layout

- What is checked: [OVERVIEW.md](OVERVIEW.md).
- What remains: [TODO.md](TODO.md).
- Comparisons with measurement: `tools/e8p/E8PConstants/PMFlavor` (`CandidateTests`, `FlavourPulls`,
  `ExperimentalPulls`); no derivation module imports them.

## Build

Lean 4.34.1, with sibling dependencies pinned through Lake. Library order: PMSubstrate → PMAction → PMConstants → PMKAutomaton → PMElementaryParticles → PMFlavor → PMHadrons → PMAtoms → PMCosmology (`AuditDependencies`). PMFlavor comes after
PMElementaryParticles because a flavour change is the label change of an event that changes protocol.

```sh
./build.sh fast PMFlavor        # this library
./build.sh fast PMFlavor.X      # one module
```

The top-level `./build.sh audit` runs the whole-tree axiom and dependency audits. Open premises are
stated in module docstrings and in REVIEW; they are not supplied by silently adding hypotheses.
