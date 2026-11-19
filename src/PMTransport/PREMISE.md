# PMTransport — working premise

There is no paper for this library. This note states what it studies so the
results have a common frame. It is a working statement, not a result.

## The system

PMTransport studies a reversible machine on E8 nodes.

| Part | In the machine | In the library |
| --- | --- | --- |
| Tape | sites with a live and a record register | `TwoSiteHandoff`, `OpenHandoff` |
| Head | the receiver at a node | exchange and bypass (`TwoSiteHandoff`) |
| Rule | exchange or bypass, controlled by a branch and a phase | `BranchPulseContract`, `RegisterControl` |
| Controller | the substrate clock (period `Δ = 43`) | `ClockPeriod`, `ClockedRootTrials` |
| Payload | a label on a generation's two walls: 2 × 8 = 16 slots | `ControlledGluedRegister` (16 channels) |

Persistence requires the machine to be reversible. It cannot erase. Every
decision that treats two inputs differently leaves a record
(`CoherentGate.unequal_needs_orthogonal`). The record must be kept, exported
or reused.

## The postulate

A persisting state that moves hands off a record. Records are payloads, and
they move by the same law.

So the cost of moving a state includes the cost of moving its records. This
is the recursion in the library: a handoff's exported records need their own
handoffs, references and clock slots.

## What must persist

Transport continues only while four things persist:

1. the carried state;
2. the reference, which needs a continuing supply (`OpenHandoff`,
   `RecordSupply`, `OddReferenceSource`);
3. the record stream, which needs renewal (an open backward orbit,
   `OpenReferenceFlow`);
4. the clock.

## Cost

A registration is one expected flagged outcome of a comparison visit. A
label's Toll counts its registrations, and the wire amplitude is
`exp(−T/2)` (`PMAction.TollAmplitude`). The price of a record is the
registrations of its write, export and reset. Which of these a visit pays is
the open "registration and record lifecycle" item in
[REVIEW-AND-NEXT](REVIEW-AND-NEXT.md).

## Generations

On the derived wire a generation is a route. The heavy generation inserts
directly. The two light generations pass through the reference node
(`ReferenceClassHop`). Every route acts the same on every label
(`GluedRegister.wallStep_class`, `crossing_walls`). So a generation is a
transport object, and a protocol difference needs a gate that reads the
label.

## Layering

`tools/layer_check.py` reports where the machine sits in the import graph.
At the time of writing, 10 of the 97 machine modules depend on no PMAction
module, and the machine needs 99 PMAction modules below it. A clean split
therefore needs one of two moves:

1. Move those 99 modules into the machine layer, or
2. move the 87 machine modules that need PMAction back into PMAction, and
   keep PMTransport to the 10 base modules and the packet-level handoff.

The first makes the native machine the base layer of the theory. The second
keeps PMAction as the base. Either choice needs a full build.
