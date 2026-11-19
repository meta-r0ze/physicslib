# PMTransport — working premise

There is no paper for this library. This note states what it studies so the
results have a common frame. It is a working statement, not a result.
The [premise ledger](PREMISES.md) tracks the checked results and open inputs.

## The system

PMTransport studies reversible internal register updates on E8 nodes and the disposition of exported records.

| Part | In the machine | In the library |
| --- | --- | --- |
| Tape | sites with a live and a record register | `TwoSiteHandoff`, `OpenHandoff` |
| Head | the receiver at a node | exchange and bypass (`TwoSiteHandoff`) |
| Rule | exchange or bypass, controlled by a branch and a phase | `BranchPulseContract`, `RegisterControl` |
| Controller | the substrate clock (period `Δ = 43`) | `ClockPeriod`, `ClockedRootTrials` |
| Payload | a label on a generation's two walls: 2 × 8 = 16 slots | `ControlledGluedRegister` (16 channels) |

Inside a system, the update is reversible: Conservation keeps the
identity-defining information (PM-1-Arch, leg update "by Conservation it is
reversible"). Every decision that treats two inputs differently leaves a
record (`CoherentGate.unequal_needs_orthogonal`). The record must be kept,
exported or reused. Once a record is exported, PM does not require that it
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

Transport continues only while four things persist:

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
registration is a separate accounting premise. Once a Toll is
supplied, the wire amplitude is `exp(−T/2)`
(`PMAction.TollAmplitude`). See the [boundary account](ADMISSION.md#boundary-erasure)
and [reversibility audit](REVERSIBILITY-AUDIT.md).

## Generations

A generation is a glue address on the wire. It names the D₄ class omitted
by its two walls. The chosen reference makes address zero direct and
sends the other two addresses through the same two-leg node
(`ReferenceClassHop`, `ReferenceNode`). The route test is shared by all
labels. The coupled wire has a heavy, a middle and a lightest mode at
bare resonance. Equal node weights leave the two restoring addresses
without individual mass ranks.

The charged lift candidate adds a pulse on the same static vector leg
for each charged protocol. The common route gives the same response to
the same offset. The label-sensitive firing law and its `Δ` scaling
remain open. The transport address, its route and the declared ledger
tiers are related in the
[generation comparison](../PMElementaryParticles/GENERATIONS.md).

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
