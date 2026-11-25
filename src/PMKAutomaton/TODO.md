# PMKAutomaton — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

The certified interface and checked results are in [OVERVIEW](OVERVIEW.md) and
[COMPONENTS](COMPONENTS.md). This file lists only the open physical admission and
named machine inputs.

## Machine interface gaps

- `U`: the physical port wiring of the certified comparator remains part of the
  admitted trace.
- The coherent receiver exchange as a root-transfer pulse of area theta, once a
  coherent amplitude is certified.
- `T`: clock calibration, serial placement and overlap.
- `L`: admitted link and successor law.
- `B`: booked export and disposition.
- `K`: tariff unit, amplitude conversion and substrate-index reconciliation.
- `D`, `J`, `Q`: detector support, shared-job mechanics and supply/acceptance
  mechanics.

## Stopping point

The interface checks reversible updates on supplied ports and histories. The physical joint update still needs reachable occupied inputs, booked outputs and a clocked recurrence. See [Admission](ADMISSION.md) and the [export contract](COMPONENTS.md#what-propagates-downstream).

## Admission

Admission is reachability under the native update from the persisting
background. An admitted trace includes its occupied ports, request and firing
guard at each tick, and the output and retained record. See the
[reachability results](ADMISSION.md).

**Paused at the mixed receiver readout.** AND and OR agree on the entire tagged
open trace. A mixed request can change the executed branch, destination and
receiver flag on the same input. The downstream consumer must therefore name
whether it reads the routed value or the paid comparison, and retain that datum
through its last use.

Two named parts remain open:

- **Background occupancy and boundary supply.** Which initial occupied wire,
  reference and controller states are accessible? For an open route, which
  further arrivals do the boundary states supply? For prior counts, what are
  the fibres of the request projection on that family?
- **Joint clocked controller.** What phase-dependent retained update connects
  the arriving ports and retained controls to the route, writer polarity and
  pulse guards? The isolated trial tick preserves its initial requests; the
  [autonomous guard test](ADMISSION.md#no-external-controller) leaves different
  reversible rules even when they agree on the tagged receiver trace.

The open admission parts and the smallest question for each:

| Open part | What it decides | Smallest question |
| --- | --- | --- |
| Spatial and receiver update | Whether the root hop, wall loader and spatial shift run, and whether the receiver exchanges or bypasses. | Which occupied port and retained branch enable each native operation? |
| Heavy writer and sampling | Which live sequence feeds the direct heavy writer, fixing the booked population or required-read set and the vacancy treatment. | Which port feeds the writer, and on which arrival does the guard fire? |
| Heavy branch and record reference | Whether either electric writer and the guarded companion crossing are admitted; paid output flags with separate balanced resets bound the remaining cost at 3/4, 27/32 or 9/10 per input for full-probe, idle-vacancy or occupied-only uniform sampling. | What jointly admits the supplied seed, polarity, record write and guarded use on both walls? Which output record is retained? |
| Lightest-offset branch | Whether the retained matched plus branch and static vector-class test drive the charged offset; its firing law also affects PMFlavor's in-cycle wall record. | Can the joint selector fire the static insertion using an occupied, retained record and preserve the calibration? |
| Label-sensitive and successive handoffs | Which crossings occur for a retained label and whether successive through probabilities multiply. | What is the through law conditional on the preceding history and its record? |
| Trial histories and phase controls | The two clocked trials preserve the initial request pair. | Which initial request fibres are reachable from the occupied EP background, and what gives their physical weights? |
| Joint schedule and Hamiltonian update | Which visits, overlaps and controls the two walls can execute; with timing and coefficient readout this fixes the schedule, ratio `r` and split walk. | Which admitted chronological word acts on the wire and record together? |
| Shared-register event ownership | Which charged-current and writer records each persisting label needs, and which are retained, reused or exported. | Which labels are present at each visit and which subsequent guard consumes each record? |

## Absolute timing

This premise fixes elapsed tick counts, available windows, cadence on both
walls and the physical wall rates. With Admission and the pulse-area and
coefficient normalization it fixes `r = K_f/|y|` and the inputs to
`LightLeakage`.

**Smallest question.** How many substrate ticks does each admitted operation
occupy, and what phase area and Hamiltonian coefficient does it realize on the
stated slots? Supply either the statistical-pair calibration on the coherent
clock or a calibrated principal-range pulse. The clock period and conditional
word bounds hold before this identification. `Interface.Handoff.principal_through_area_eq`
recovers the area for a supplied principal through pulse and the geometric current law.
The admitted port, principal branch, duration and conversion into the wall coefficient
still need to be established.

## Registration tariff

This premise converts comparison flags and unmatched preparation,
polarity-control, export, reset, renewal and maintenance jobs into paid
registrations. It decides the signed remainder in the reference comparison and
the Toll for each label.

**Smallest question.** For the admitted traces in common units, which visits
register and what is the difference in paid work after matching the same jobs at
their required state and time? Admission determines the visits and continuing
branch; the unit erasure account prices only a supplied disposal event.

## Sustained reference supply

This premise decides the occupation and lifetime of the reference and record
train, and whether either writer can use maintenance already performed by a
refresh.

**Smallest question.** Which occupied odd seed and axis supplies the required
reference at each admitted visit, and where does its displaced record go when
the reference is renewed? The supply and open-orbit theorems hold for supplied
states and routing; the physical states, resets and renewal times are the input.

## Disturbance and acceptance

This premise gives the viability margin of a sustained handoff under the stated
disturbance.

**Smallest question.** Which incoming reference errors may the receiver accept
at its admitted visits? The acceptance equivalence is independent of Admission;
its physical tolerance and incoming disturbance must be attached to the admitted
operation and supplied orbit.

## Layering

This is a build-boundary choice. PMAction and `PMKAutomaton.Machine` share
finite dependencies; the packet interface sits above PMConstants. The clock
reading is shared through `Machine.ClockRing` and the native axis hop no
longer imports packet-layer placement.

**Smallest question.** If a stand-alone machine build is needed, which common
finite base will the two layers import, with the existing module paths preserved?
The current boundary includes `StateIdentification`, `CommonResponse`,
`ChiralityConvention`, `InvolutionComparison`, `RestorationResponse`,
`SelectedSampling`, `SubstrateReflection` and `GaugeRecordEmbedding`. This choice
is independent of physical Admission and remains parked.
