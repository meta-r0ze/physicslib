# PMElementaryParticles — open work

See [SCOPE](../../SCOPE.md#named-premises) for the shared premise statements.

## Occupancy cost

- Derive one recurrent occupied E8 program for each visible class and generation (`EPSpine.Program`).
- Close its update and prove Capacity, Margin, Map, Protocol, Toll and Governor on the same execution (`ProgramWitness.Pillars`).
- Identify occupied resources and their capacity values on the native clock (`PMKAutomaton.Interface`).
- Sum the cost over one full recurrence in one capacity unit. Count each required resource once at each booked visit (`CommonResponse.bookedCapacity`).
- Derive a physical mass unit and compare the resulting values in e8p only after the recurrence and its accounting are proved (`SharedUnits`).

## Placement and composition

- Choose the physical vacuum, sector placement and map from `refRecord` to the D₄ reference (`SharedReference`, `ColourReference`).
- Define the joint 43-ring state and prove alone/together closure (`RingSurvivors`, `ProgramWitness.Pillars`).
- Characterize all 43-ring firing patterns at the Margin ceiling (`RingSurvivors`).

## Decay and current

- Attach the carrier current to the physical contact vertex and final states (`CarrierTransitionOperator.substrateOperator`).
- Assemble the second-stage radiative diagram kernel (`MuonQEDLoops`).
