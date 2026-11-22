# PMElementaryParticles — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).
This file is the open list only.

## Line and ring

- **Finish replacing `sectorBasis`.** The old D4 coordinates disagree with the
  clock plane (slice roots change the reading by `0` or `±6`).
  `AlignedSectors.alignedSectorBasis` is the aligned placement and
  `ChannelPlacement` uses it. `PMSubstrate.Vacuum` and `PMSubstrate.Channels`
  still use `sectorBasis`; move them and recheck their results.
- **Characterise the Margin ceiling on the 43-ring.** `RingSurvivors` proves
  the Toll floor and least Toll for every firing pattern, and one saturating
  (trapping) pattern. The exact set of patterns with utilization `1` is not
  stated. Do it only if a downstream result needs it.
- **Say what the clock-silent roots do.** The 22 roots at phase `0` do not move
  a packet around the ring. Identify their role as internal or transverse
  motion and its observable consequence.
- **Alone/together on the 43-ring.** Single-protocol survivors are restated on
  the 43-ring (`RingSurvivors`). The alone/together (several protocols on one
  ring) result is still the 3-ring computation.

## Composition and vacuum

- **Choose the vacuum.** Both candidate references are single-site states:
  lepton `+e₀` and the colour-symmetric state. The P4 shared-vacuum tables
  remain the comparison; no shared vacuum is valid for all four record classes.
- **Settle shared versus sector-local or composite placement.** The blocker is
  the vacuum/reference choice, not the line map: two D4 sectors and a stationary
  connected background are certified, but the record-class-to-sector assignment
  is not.
- **Reference identity.** `refRecord` is not proved equal to `SharedReference`
  or `ColourReference`. The blocking item is the E8/layout reference map from
  the finite record to a D4 minimal-vector class.
- **Multi-protocol composition.** Define the composite state for `k` protocols
  on one 43-ring from the nested-paper rules. Alone/together closure cannot be
  decided until that joint state exists.

## Generations and costs

- **Derive the step-to-cost rule for the coset signatures.** The certified
  signatures are vector `(7,7,2)`, spinor `(4,4,0)` and conjugate spinor
  `(4,4,8)` for forward, backward and silent wall crossings. A cost per period
  must use the one-tick count for the heavy-to-light step and may use silent
  steps only to split the two light generations.
- **Complete the charged lift.** The static selector supplies no inverse power
  of `Δ` for the offset. A native selection and firing law, the offset's
  scaling, and the existence of shared calibration remain open.

## Everything else still open

- **Elementary masses and widths.** Derive the assignment of invariant costs to
  lepton and quark tiers, the allowed transition histories and their rates.
  Connect the charged-current operator to the physical contact vertex and
  final-state readout; the blocker is the carrier-to-protocol contact and
  readout map.
- **Radiative stage 2.** This is not started. The blocker is the assembled
  diagram kernel, not an individual loop integral.
- **Legacy single-reference assumptions.** The heavy writer's single reference
  is not certified; the choice is conditional per label. The blocker is the
  background/vacuum choice above.
