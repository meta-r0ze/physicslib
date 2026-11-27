# PMKAutomaton

PMKAutomaton describes state and record transfer between E8 nodes. It is an E8
persistence automaton: a reversible cellular automaton on the E8 substrate.
Import `PMKAutomaton.Interface` for the handoff, record, cost, clock and
route and embedded symmetry theorems. Import `PMKAutomaton.Values` for the checked numbers and
their conditions. Use [the component inventory](OVERVIEW.md#component-contracts) and
`PMKAutomaton.Components` to locate the open contracts.

Run `./build.sh lean PMKAutomaton.Interface PMKAutomaton.Values PMKAutomaton.Components` for a
targeted check. The library build is `./build.sh PMKAutomaton`.

The [overview](OVERVIEW.md) lists the results and links to the module notes.
The [clock section](OVERVIEW.md#clock) gives the pulse constraints.
`ClockSymmetryGenerators` certifies the full aligned clock-root stabilizers;
the [symmetry table](OVERVIEW.md#full-clock-root-symmetries) states their scope. The [open list](TODO.md) lists the
remaining physical inputs.

## The system

PMKAutomaton studies a lattice of E8 nodes. In the encoded line and ring
models the same local rule acts at every site with a common phase. The
lattice view names the parts and ports. The complete joint update for
the carrier packet and retained controls remains open.
The [joint-successor audit](OVERVIEW.md#constraints-on-occupied-joint-successors)
states the resource and primitive-event definitions needed before classifying it.

| Part | Role at a node | In the library |
| --- | --- | --- |
| Registers | Live and record stream slots, plus retained controls | `TwoSiteHandoff`, `LocalController` |
| Receiver | Exchange or bypass on two arrivals | `TwoSiteHandoff`, `OpenHandoff` |
| Rule | Local guard and branch-dependent pulses | `LocalController`, `BranchPulseContract`, `RegisterControl` |
| Clock | Shared phase with period `Δ = 43` in the certified clock models | `PMSubstrate.E8Values`, `ClockedRootTrials` |
| Link and payload | Directed transfers and two-wall packet labels with 16 slots | `OpenReferenceFlow`, `GluedRegister`, `PacketGaugeActions` |
| Boundary | Keep, recycle or erase a supplied export | `BoundaryErasure` |

The [component inventory](OVERVIEW.md#component-contracts) gives the remaining parts and
the scope of their connections.

Inside a system, the update is reversible: Conservation keeps the
identity-defining information (PM-1-Arch, leg update "by Conservation it is
reversible"). Every decision that treats two inputs differently leaves a
record; the checked record statement is in the [record results](OVERVIEW.md#record).
The record must be kept, exported or reused. Once a record is exported, PM does not require that it
is kept. It can be erased, and the erasure is paid as Toll. In the standard thermal setting Landauer gives
a lower bound of `k_B T ln 2` for one unbiased bit. The boundary account
uses one Toll unit per booked binary erasure. Conservation protects the
retained registers across the update.

## The postulate

A persisting state that moves hands off a record. Records are payloads, and
they move by the same law.

So the cost of moving a state includes the cost of moving its records. This
is the recursion in the library: a handoff's exported records need their own
handoffs, references and clock slots.

## What must persist

KAutomaton continues only while four things persist:

1. the carried state;
2. the reference, which needs a continuing supply (`OpenHandoff`,
   `RecordSupply`, `OddReferenceSource`);
3. the record supply. The retained-stream model uses an open backward
   orbit for uninterrupted arbitrary-disturbance restoration
   (`OpenReferenceFlow`);
4. the clock.

## Cost

A booked boundary erasure pays one unit per exported bit reset.
A comparison supplies a flag probability. Its use as a paid
registration is a separate accounting premise. See the
[boundary account](OVERVIEW.md#reversibility-boundary), the
[cost results](OVERVIEW.md#cost), and the
[reversibility boundary](OVERVIEW.md#reversibility-boundary).

## Generations

A generation is a glue address on the wire: it names the D₄ class omitted
by its two walls. The reference choice and the direct and restoring route types
are checked in the [route results](OVERVIEW.md#route). Joint firing and clock placement remain open. See the [open list](TODO.md). The transport
address, its route and the declared ledger tiers are related in the
[generation comparison](../PMElementaryParticles/OVERVIEW.md#generations-on-the-e8-wire).

## Layering

`tools/layer_check.py` reports where the machine sits in the import graph.
At the time of writing, 10 of the 97 machine modules depend on no PMAction
module, and the machine needs 99 PMAction modules below it. A clean split
therefore needs one of two moves:

1. Move those 99 modules into the machine layer, or
2. move the 87 machine modules that need PMAction back into PMAction, and
   keep PMKAutomaton to the 10 base modules and the packet-level handoff.

The first makes the native machine the base layer of the theory. The second
keeps PMAction as the base. Either choice needs a full build.

`AutonomousCensus` gives native cycle-rate proofs; `AutonomousCensus43` checks the
rate-one static witness and its failed marker robustness. The finite cycle census is
reproducible with `tools/autonomous_ring_census.py`; it is not a kernel certificate.
