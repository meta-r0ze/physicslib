# Reachability of native transport traces

## Starting state

| Certificate | What it fixes | What the physical initial state still needs |
| --- | --- | --- |
| `CarrierVacuumSector.range_iff_odd`, `identification` | The accessible carrier representation is the antipodal-odd sector of each class, with the stated Hamiltonian readout. | The occupied sites, class and amplitudes. The sector contains coherent states. |
| `RegisterVacuum.isometry`, `evolution_readout`, `IndependentRegisters.occupied_encode` | The occupied two-bank encoding and its evolution for supplied inputs and parameters. | The physical occupation sector and contents of each bank, including the request register. |
| `NativeReferenceBackground.stationary_iff`, `referenceField_fixed`, `minimum_in_family_iff` | For the specified connected finite update, the live and record copy of each active mode share one common value throughout the connected orbit. This applies in particular at a node and its neighbours. Other fields are free. A stationary witness in the accessible family minimizes the specified positive excess price. | The neighbourhood update and accessible occupation family. The common value is free even in the stationary family. In the linear field model zero and nonzero common fields are stationary. |
| `SharedReference.reserved_single`, `shared`, `ReferenceEconomy.economy_selects_lepton` | Maximal payload with a nonempty reservation gives one cell for both refreshes. The allocation model selects the lepton type under colour preservation. | The occupied state arriving at a writer and the map from the reserved cell to its timed ports. |
| `OddReferenceSource.rest_stationary`, `rest_modes_distinct`, `rest_population`, `odd_seed_train_restores` | In each class and on each wall there are two distinct exhibited unit-population rest seeds. The loaded first-wall vector seed gives a ready reference on the open route when supplied before each visit. | Which modes the background actually occupies, and which ready values feed the route. The finite index `Fin 3 × Bool × Bool` lists the coordinate seed witnesses. There is no completeness or accessibility certificate for this list as an initial-state family. |

The fixed-field and supply theorems describe different parts of the
problem. On an exactly homogeneous live and record pair, the supplied
finite update preserves the same contents. A packet reaching the writer
needs a specified excitation or incoming stream on that background.
`OpenHandoff.acceptance_iff_supply` constrains readiness on one line.
`any_incoming_trace` allows independently specified traffic on the other.
The family of physically accessible initial microstates has no finite
encoding in the present results. There is no basis for counting it as the
coordinate witnesses, a product of independent ports, or the uniform
packet inventory.

**Background occupancy and boundary supply.** Specify the accessible
occupied configurations, including excitations and controller states, and
the incoming boundary contents for the chosen clock horizon. To count
priors, give a finite enumeration or a certified finite quotient with
its fibre sizes.
