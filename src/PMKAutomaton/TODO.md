# PMKAutomaton — open work

**Interface closed. Physical admission open.** EP should import
`PMKAutomaton.Interface` for the certified operations and
`PMKAutomaton.Values` for conditional rates and thresholds. A
physical EP conclusion needs its admitted path, reader, booked
work and traffic. See the [closeout](COMPONENTS.md#kautomaton-closeout)
and [ranked inputs](COMPONENTS.md#remaining-free-inputs-by-reach).
The [bare-line result](COMPONENTS.md#bare-line-stabilizer) separates
the mathematical stabilizer from the directed marked carrier encoding.

`PMElementaryParticles.IsolatedExcitation` defines the O-sector for the object
a mass refers to: vacuum plus one packet label. `IsolatedReceiverTrace` embeds
it into `RingReceiver.State 3` and iterates `tick`; the receiver registration
column is zero under AND and OR, so the rules tie. The record Toll is a
separate column with no certified common ledger. The hold/FIFO packet lifts do
not determine booking ticks. The [admission chain is paused](#stopping-point) at the
mixed receiver readout required by a downstream trace. The
[component inventory](COMPONENTS.md#interactions) locates the open inputs
across the lattice at once. The mixed readout is in X → E, D → E and F → E.
The [regress map](COMPONENTS.md#where-the-earlier-questions-sit) links
earlier questions to their cells. See the
[ranked free inputs](COMPONENTS.md#remaining-free-inputs-by-reach)
for the remaining dependencies. The projected core and the
16-slot FIFO lift reversibly. Their joint firing rule and the
clocked EP reader still need a physical attachment.

## Stopping point

The admission chain is paused at the mixed receiver readout required by a
downstream trace. The certified EP formulae take no such receiver trace as an
input. See [Admission](ADMISSION.md) and the
[export contract](COMPONENTS.md#what-propagates-downstream).

## Closeout list

**Moved to EP:** the retained request field and firing pattern G; the
excitation occupancy and reference-record choice O; the label record, reference
and theta in U; which label record W reads; the label Toll/paid-event part of
K; and the history/prior family H. `IsolatedReceiverTrace` and
`RecordPortIdentification` are EP protocol work that use the KAutomaton
machine. The certified label dependence is `bitToll_eq_hamming`, `refRecord`,
`bitRingTotal43_eq` and `firingPattern`.

**Remaining KAutomaton-only work:**

- `U`: **flag identification done.** The certified comparator
  `CoherentComparisonRepair.compare (phase x)` converts the phase encoding to
  orthogonal records; `PhaseToRecord.minus_probability` gives
  `DiagonalReadout.flag x`, and the expected receiver flag is `flag x`
  (`expected_receiver_flag`). The factor-two normalization is only the two
  encodings. The physical port wiring remains part of the admitted trace;
- the coherent receiver exchange as a root-transfer pulse of area theta (a
  machine property, once a coherent amplitude is certified);
- `T`: clock calibration, serial placement and overlap;
- `L`: admitted link and successor law;
- `B`: booked export and disposition;
- `K`: tariff unit, amplitude conversion and substrate-index reconciliation;
- `D`, `J`, `Q`: detector support, shared-job mechanics and supply/acceptance
  mechanics.

Everything else in the old protocol list is either derived, hypothesised in the
certified machine, or moved to EP. The bit-ring model remains an EP hypothesis,
not a KAutomaton result.

## Closeout

KAutomaton machine work is closed on the conditional interface. The receiver
flag computation W and guard table G are certified. The common comparator U's
flag identification is certified through the phase-to-record converter
(`PhaseToRecord.converter_unitary`, `minus_probability`,
`expected_receiver_flag`). The coherent encounter is certified
(`encounter_unitary`) with pass/flip amplitudes `(1 ± e^{ix})/2`; at `x=π`
it is a full flip (`exact_bit_flip`). The full-ring Lean spectrum block proof
was not completed, but the script verifies `cos E(k)=cos(x/2) cos k` exactly.

What remains is listed as named machine inputs on the conditional interface:
T (clock), L (link), B (boundary), D (detector support), J (jobs), Q
(supply/acceptance), and the tariff unit. The mass reading of the spectrum is
an EP hypothesis, not a KAutomaton result.

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
| Trial histories and phase controls | Whether the physical controller realizes the four retained two-request histories with equal prior counts, or whether a principal-range calibration is used. | What are the initial request fibres, and which clocked comparison uses them? |
| Joint schedule and Hamiltonian update | Which visits, overlaps and controls the two walls can execute; with timing and coefficient readout this fixes the schedule, ratio `r` and split walk. | Which admitted chronological word acts on the wire and record together? |
| Shared-register event ownership | Which charged-current and writer records each persisting label needs, and which are retained, reused or exported. | Which labels are present at each visit and which subsequent guard consumes each record? |

## Absolute timing

This premise fixes elapsed tick counts, available windows, cadence on both
walls and the physical wall rates. With Admission and the pulse-area and
coefficient normalization it fixes `r = K_f/|y|` and the inputs to
`LightLeakage` and `WallGapCalibration`.

**Smallest question.** How many substrate ticks does each admitted operation
occupy, and what phase area and Hamiltonian coefficient does it realize on the
stated slots? Supply either the statistical-pair calibration on the coherent
clock or a calibrated principal-range pulse. The clock period and conditional
word bounds hold before this identification.

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
finite dependencies; the packet interface sits above PMConstants.

**Smallest question.** If a stand-alone machine build is needed, which common
finite base will the two layers import, with the existing module paths preserved?
The current boundary includes `StateIdentification`, `CommonResponse`,
`ChiralityConvention`, `InvolutionComparison`, `RestorationResponse`,
`SelectedSampling`, `SubstrateReflection` and `GaugeRecordEmbedding`. This choice
is independent of physical Admission and remains parked.
