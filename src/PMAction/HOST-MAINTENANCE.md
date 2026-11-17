# The reference-maintenance host

The candidate outer system is the reference-maintenance machine: native carrier
banks, the reference-restoring interaction, routing and any record supply. The
existing construction identifies an executable host model; it does not uniquely
select the physical allocation or the interaction with the flavour wire.

A proposed physical mechanism should identify its maintained task, state,
resource boundary and six-pillar contract. Reusable algebraic lemmas can support
several such systems. Assigning the six names alone does not supply an update,
interaction, source or cost law.

## Six pillars and their present implementation

| Pillar | Existing construction | Still to identify from the substrate |
|---|---|---|
| **Capacity** | `ActualRootRepair` uses exactly four moving vector-carrier labels: two live and two record modes. `VectorEvenFrame` supplies four even modes; `ReferenceRootRecord` uses them on a separate bank. | Which banks coexist physically and which modes belong to each protocol. A direct sum of modes is not an independent tensor factor. Do not count one bank twice. |
| **Map** | `RecordSupply.disturbance_exported` retains each arriving live value in the outgoing record. The class writer retains the actual carrier class with orthogonal markers. | Which distinctions the actual task must retain, and whether it needs that class writer rather than another maintenance scheme. |
| **Protocol** | `NativeCarrierProtocol.lookup` streams in opposite directions and applies the existing root at the coupling site. `ActualRootRepair.repair` exchanges the encoded live and record modes. | Which native sequence couples this machine to the restoring node. The reference protocol and vacuum split are distinct observed operators. |
| **Governor** | The supplied routing fixes where coupling occurs; unused labels are fixed. The class-pair accept-or-idle governor preserves its validity domain. | The restrictions enforcing the host's maintained identity. Pair validity alone does not select those restrictions. |
| **Toll** | `ReferenceMaintenance.minimum_executable_cost` gives the least additive work for the stated jobs. `ActualRootRepair` separates label-event prices from coherent responses. | Native prices and durations for joint controls, preparations and record routing; conversion of admittance into a Hamiltonian rate. |
| **Margin** | Clean incoming records restore arbitrary arriving live packets. Finite rings return the old disturbance; open translation routing avoids return under its source contract (`RecordSupply`). | Actual disturbance family, required repair horizon, physical routing and a matching incoming reference supply. An unbounded substrate alone does not specify that incoming state. |

## Where information crosses the boundary

At the supplied coupling site, the incoming record becomes the live output;
the arriving live value becomes the departing record. This is the exact content
of `RecordSupply.live_at_site` and `disturbance_exported`. No distinction is erased.
Restoration requires the incoming record to match the reference
(`ActualRootRepair.clean_record_iff`). Occupied records can be transported, but
cannot be silently reused as clean ones.

The native live and record channels here are direct-sum modes of one carrier
bank. They are not automatically the two tensor subsystems used by a
record-only no-feedback argument.

## What can leave the node readout unchanged

[ReferenceHostInterface.lean](ReferenceHostInterface.lean) establishes three
separate facts, without assuming a product initial state:

1. **Independent export.** If the record-bank operation is `1 ⊗ U` with `U`
   unitary and the node observable is `J ⊗ 1`, every live quadratic readout is
   unchanged. The actual native routing permutation passes this test when
   allocated to a separate bank. The bank can be occupied or entangled with the
   live state. Cleanliness is needed for restoration, not for this transport identity.
2. **Writing.** The class-controlled write using the actual even carrier markers
   compresses `J` to its class-block diagonal part. It preserves the full observable
   exactly when `J` has no cross-class entries. Independent export afterward
   adds no further change, but does not undo the write's change.
   `pair_current` / `series_write_changes` test a concrete conserving two-port
   response: it fails preservation if its endpoints are different classes on
   the recorded factor. Whether those endpoints and the recorded reference
   belong to that same factor remains a native allocation question. This is an
   all-input observable contract, stronger than preserving one class-definite
   stationary reference. It does not rule out a maintenance scheme that permits
   disturbance followed by restoration.
3. **Shared-bank coupling.** The existing maintenance root exchanges the live-port
   and record-port projectors. It fails the live-port no-feedback test, despite
   being conservative and exporting the old value. Its name or routing direction
   does not make it a record-only tensor operation.

There is a concrete routing mismatch for the proposed class-record bank:
`two_markers_stuck` / `two_markers_stuck_iterates` show that the existing stream
fixes the second and third spatial markers at their original sites. Its moving
carrier labels cover axes 0 and 1, while those markers occupy axes 2 and 3.
Consequently this stream alone does not export the entire proposed class record
or renew its blank for arbitrary class-record inputs. The following circuit
resolves the finite routing obstruction without restricting the class domain.

## Export as a six-pillar subsystem

[ReferenceMarkerExport.lean](ReferenceMarkerExport.lean) uses the existing native
transport factor, with its on-site maintenance coupling omitted, conjugated by
certified simple-root words. A word exchanges axis 1 with the selected spatial axis while fixing
axis 0. Thus each spatial marker can use the same record channel in turn.
After one pass per spatial marker, all three tag streams move one neighbour in
the record direction; the blank stream moves oppositely through three neighbours.
These are macrocycle displacements, not physical rates or a selected tick.

| Pillar | Checked construction and retained obligation |
|---|---|
| **Capacity** | All four existing even marker modes fit in the same carrier bank. Physical allocation of that separate bank remains supplied. |
| **Map** | `export_spatial` / `localized_export` retain each class marker and its amplitude while moving it. `export_unitary` preserves the whole bank state, including the blank. |
| **Protocol** | `rename_root_word`, `native_stream_eq` and `export_eq` certify the three-pass circuit from existing root words and the supplied transport factor. This proves an available schedule, not its selection or price. |
| **Governor** | Relabelings fix the blank axis; export acts on the record bank. `no_feedback` preserves every live observable under the independent-factor contract. Physical bank isolation and access to the separate transport factor remain to establish. |
| **Toll** | The circuit exposes every relabeling word and transport pass. Native implementation prices, time per pass and optimality remain open. |
| **Margin** | `ReferenceMarkerSupply.finite_supply` derives clean local ports over a non-return horizon from the initial prepared modes; `lattice_supply` permits arbitrary finite times on nonzero translation routes. Initial source preparation/normalization and physical repair timing remain supplied. |

There is no erasure or new bank copy in this construction. Blank transport is
included in the permutation, rather than silently restored at the old site.
The local blank condition concerns coherent amplitude modes; it does not by
itself allocate normalized independent record registers at every site or prove
an unlimited reservoir.

[ReferenceMarkerSupply.lean](ReferenceMarkerSupply.lean) now attaches the circuit
to a repeated-write schedule. Every cycle is an actual site-local root-word
write followed by export. The supplied class sequence controls permutations,
and finite histories lift to unitaries; no field is overwritten with a newly
prepared blank. History-control labels can remain coherent. This does not
select the class-input task or prove that a pure reference's full reduced state
is preserved by writing.

The incoming-path theorem follows each mode back through the initial field
until it encounters the writing site. It yields clean local amplitude ports for
T cycles from prepared incoming modes and the no-return condition for that
horizon. Nonzero lattice translations supply open routes using the existing
`RecordSupply.translation_open`; both the tag and three-step blank routes are
then open. Per-cycle cleanliness is a consequence under this initial source
contract, rather than a new assumption after every write.

[ReferenceReadySource.lean](ReferenceReadySource.lean) narrows the initial-source
contract further. In the admitted even bank, a **ready** port has zero overlap
with all three written class markers. Completeness forces that profile to be a
scalar multiple of the blank; if a local normalized profile is required, the
scalar has unit modulus. This is a consequence of the stated task/readouts,
not a selection of the task or a claim about source preparation.

If this ready field is stationary under the unwritten export transport, its
amplitude is constant along each blank donor orbit. That suffices for repeated
writes: a globally specified uniform field is unnecessary, and unrelated donor
orbits need not have equal amplitudes. `ready_population` retains the same ledger
on the local orbit. A uniform field of an already-written tag is stationary too,
so transport stationarity and an excess-price minimization alone do not establish
readiness. The source's admissible family must include the actual readiness task
and an accessible appropriate background. Existing selection statements do not
supply that accessibility or fix a reference value.

The Capacity and Margin cost of this construction is explicit: T fresh arrivals
need T+1 distinct bank sites including the initially local blank. For a matching
blank amplitude a, the initial population on those distinct blank donors is
(T+1)|a|². On open routes a nonzero uniform source therefore has arbitrarily
large population in finite incoming regions. Repeated routing does not create
that source, select its normalization, or identify an infinite uniform field
with a normalized one-particle state.

These are observable identities, not a proof of zero static admittance or a
choice of the node current. The next obligation is to identify the native node
observable and its encoding, test **every** interaction across the host boundary,
and establish the applicable static response.
[ReferenceNodeBoundary.lean](ReferenceNodeBoundary.lean) then gives `α/2` for a
closed, conserving steady host attached only at the node, while an independently
anchored port contributes a load. Open record transport can coexist with an
unchanged node readout under the independent-factor contract above; that contract
still needs native allocation and joint-interaction checks.

## A coherent flip that restores the even record sector

[PairedRootFlip.lean](PairedRootFlip.lean) supplies an all-class native-root
construction for a completed coherent beta rotation. Mirrored root phases
cancel their scalar terms; the spinor class uses an additional phase
conjugation and its inverse. The net operation has the required coordinate
rotation and restores every even mode, so every observable supported on that
even record sector is unchanged at the end. It needs no extra bank. The result is a class-indexed circuit family; coherent
class-controlled scheduling or a single class-blind compilation still needs
a native realization. This preserves a direct-sum sector; it does not establish independent tensor registers.

For this subprotocol, Capacity is the existing eight carrier labels, Map is
the retained odd/even state, Protocol is the certified root-phase sequence,
and Governor is the exact final even-sector identity. Toll must count the
whole scheduled word, and Margin must allow its intermediate even-mode motion
and time before restoration. An inverse phase parameter can be replaced by
the remainder of a forward phase period; the added time is part of that ledger.
The angle parameter is not a physical event duration.

This closes availability of a completed coherent beta circuit under the
existing phase-control contract. It does not select that circuit as the
native event, calibrate its rate, preserve every even mode during intermediate
pulses, or complete the other factors of the full walk. It also does not remove
the offset of a single lazy wall event by a gauge convention: it is a different,
explicit composite operation.
