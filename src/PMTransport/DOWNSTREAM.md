# Receiver rule and downstream quantities

This inventory separates fixed inputs and conditional formulae from
observations of a receiver trace. The latter can see the rule even
when the former have no receiver argument.

| Surface | What it supplies | What the receiver rule could change |
| --- | --- | --- |
| `Values`, clock | `Delta`, `shortSerialTicks`, `longSerialTicks`, their minima, `shortSerialR`, `longSerialR`, and `equal_normalization_rate`. | The period, serial budgets and normalized ratios have fixed arguments. A physical choice of word, overlap or timing is a separate trace input. |
| `Values`, thresholds | `outputFlagThreshold`, `balancedResetThreshold` and their case values. | These are fixed functions of sampling and flag accounting. The selection that uses them also needs the actual booked costs. |
| `Interface.Handoff` | The two-site step and destinations, repair and return, flags, half-pulse, left outflow, conductance, and independent through paths. | Which branch fires controls the live and record destinations and whether the exchange comparison runs. The coefficient `α`, the stipulated current law, and the independent-path formula are fixed at the same premises. |
| `Interface.Record` | Open receiver and export traces, their population and supply, odd reference preparation, retained restoration, orthogonality and the register-control and pulse contract. | A different port order can change which live state is restored and which value is retained or routed on. The tagged open route agrees in both rules. The preparation and storage requirements apply to their specified inputs and operations. |
| `Interface.Cost` | Expected counts, diagonal flags, `scheduleToll`, survival and amplitude, selection and refresh. | Costs can change if the booked encounters differ. The cost and amplitude maps and the minimum theorem remain the same for the same arguments. |
| `Interface.Clock` | Period, quarter and half pulses, word lengths, slot histories, priors conditional on preparation, and clock calibration. | At a common start the retained requests, probe and clock advance independently of the guard. A distribution over different starts and an admitted physical schedule are further inputs. |
| `Interface.Route` | Wall orientation, glue address, stationary reference-class test, direct and restoring paths, two equal legs and the crossing identities. | The predicates and effective series weight `α/2` at the stated assumptions are fixed. A live packet's actual route through a mixed-request receiver can differ. |
| EP tier and mass ledger | `TierLedger.tiersFor`, `QuarkMasses`, `LeptonMasses`. Their inputs are the declared tier lists, substrate counts including `Δ`, `D`, `sigma`, `chi`, and the supplied overhead, charge and conversion constants. | There is no receiver-rule argument in the tier lists or mass formulae. These values give no identification of a selected wire mode with its tier. |
| EP insertion and schedule | `HeavyFlipControl`, `HeavyFlipRecords`, `ElectricHeavyRecord`, `ChargedInsertion`, `ProtocolToll`, `WireSchedule`, `WireReferenceCost`. The heavy word and candidate light offset use supplied label, address, reference, record, phase and booked costs. | The selector identities and flag and amplitude formulae are fixed for their arguments. An effective insertion, writer input, or chosen reference can only depend on a receiver rule through a certified embedding of that trace and its paid work. |
| EP packet readers | `VacancyProjection`, `ElectricCoordinateDecoder`, `RefreshMap` and the native frame, branch-encoding, register and carrier readers. | The operators act on supplied slots and tags. They have no attachment to the mixed-request receiver. |

The direct EP imports are `Interface` from its umbrella and
`HeavyFlipRecords`, `HeavyFlipControl`, `VacancyProjection`,
`ElectricCoordinateDecoder`, `RefreshMap`, `WireSchedule` and
`ProtocolToll`. `WireReferenceCost` imports `Values` for the two
threshold accounts. The direct machine imports in EP provide carrier
frames, root readout, triality, register interaction and branch
encoding. They precede the AND/OR controller.

Flavor uses the same interface for `LinkFlux`, `ExchangeChirality`,
`MassTermLaw`, `AllRootRestoration`, `RootRepairSelection` and
`HalfTurnAperture`. `ReferenceSafeRestoration` uses the machine root
order comparison. `FlavourPulls` reads the two normalized serial
ratios for its labelled comparison. None of these or the EP modules
imports `LocalController`, `RingReceiver` or `BoundaryErasure`.
The Transport umbrella also exposes those three model modules, so
their observable trace differences matter to a claim of machine symmetry.
