# PMTransport — transport between E8 nodes

PMTransport describes how a state moves from one node to the next.
A node is a site with registers for the state and its record.
A handoff is the transfer of a state through a node.

## How a handoff works

1. Move the incoming state to a receiver register.
2. Pass the state through the node or exchange it with the receiver reference.
3. Send the outgoing state to its next register and keep the required record.

The native machine supplies carrier moves, reversible register operations, and a clock model.
The handoff model gives the outputs of a pass or an exchange.
The results give the conditions for each operation.
The physical clock and registration cost need more work.

## How to use the library

- Import `PMTransport` to use the handoff results and the native machine.
- Import a module in `PMTransport.Machine` to use one native operation.
- Read [OVERVIEW.md](OVERVIEW.md) to find the results.
- Read [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) to find the open work.

## How to check the library

1. Run `./build.sh PMTransport`.
2. Run `./build.sh audit` after you build the downstream libraries.

The machine builds with PMAction.
The handoff layer uses results from PMConstants.
The particle libraries use PMTransport to implement their protocol operations.

This README uses [ASD-STE100 Simplified Technical English](https://www.asd-ste100.org/about_STE.html).
