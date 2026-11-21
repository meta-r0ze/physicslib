# PMElementaryParticles — open work

Current detail is in [HISTORY.md](HISTORY.md). This file is the open list only.

## Line problem

See [LINE-AND-COMPOSITION.md](LINE-AND-COMPOSITION.md).

- State the update model: one receiver tick is one root event.
- State Closure for the equal weights on the tick steps.
- Replace `sectorBasis` with an aligned placement, or state the alignment as a
  named hypothesis, and recheck the modules that use its coordinates.
- Replace the 3-ring registration counts with 43-ring results.

## Composition problem

See [LINE-AND-COMPOSITION.md](LINE-AND-COMPOSITION.md).

- Choose the vacuum: lepton `+e₀` or the colour-symmetric state; use the P4
  shared-vacuum tables.
- Fix the triality orientation of the aligned-clock cosets and state the rule
  that turns step counts into cost per period. It must use the one-tick count
  for the heavy-to-light step.

## Full-ring Lean spectrum

- Prove the momentum action, the explicit `M(k)`, its trace/determinant and the
  eigenvalue identity `cos E(k)=cos(x/2) cos k`.
- Prove the empty-firing spectrum gapless.

## Everything else still open

- **Elementary masses and widths.** Derive the assignment of invariant costs to lepton and quark
  tiers, the allowed transition histories and their rates, and connect the charged-current operator to
  the physical contact vertex and final-state readout. Blocking item: the carrier-to-protocol contact
  and readout map.
- Shared vs sector/composite background: no certified placement of the
  bit-ring background or selection of the colour composite. Blocking item:
  the line/placement map.
- Reference identity: `refRecord` is not proved equal to `SharedReference` or
  `ColourReference`. Blocking item: the E8/layout reference map.
- Multi-protocol composition: same missing object as above.
- Triality and per-generation costs: conditional on the line/attachment map.
  Blocking item: the bit-ring-to-lattice line.
- Radiative stage 2: not started. Blocking item: assembled diagram kernel.
- Legacy single-reference assumptions: conditional per label; the heavy writer
  single reference is not certified. Blocking item: background choice.
